#!/usr/bin/env python3
"""Daily refresh: re-pull live Silver Bulletin + FEC inputs and regenerate site/data.json.

Standard library only (urllib, csv, json). Designed to run unattended from
GitHub Actions. Reuses the exact math from scripts/build.py so the output
shape and field semantics never drift from what site/index.html expects.

Failure policy:
  - Silver Bulletin data (the forecast itself) is load-bearing. If it cannot
    be fetched, this script fails loudly (non-zero exit) rather than writing
    stale or partial data.
  - FEC money data is best-effort. If the FEC pull fails outright, we fall
    back to whatever money fields (receipts/coh/proj/rate/cov/match) already
    exist for that race in the previous site/data.json, so the site keeps
    working (with a floor value) rather than breaking the whole refresh.
"""
import csv
import datetime
import io
import json
import math
import os
import re
import sys
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
BASE = os.path.join(HERE, "..", "data")
SITE = os.path.join(HERE, "..", "site")
DATA_JSON = os.path.join(SITE, "data.json")

SIG = {"H": 6.65, "S": 6.69}
ELECTION = datetime.date(2026, 11, 3)
CYCLE_START = datetime.date(2025, 1, 1)
MONEY_FLOOR = 250_000.0

DEFAULTS = dict(c_house=2.0, c_senate=2.0, sen_val=13.05, eta=0.5, money="proj", theta=0.0)

# Datawrapper chart ids + a known-good version to start probing upward from.
CHARTS = {
    "house_vpi": dict(chart_id="1Ixth", known_good=42, kind="vpi", ch="H"),
    "senate_vpi": dict(chart_id="mrCsL", known_good=45, kind="vpi", ch="S"),
    "house_candidates": dict(chart_id="NX4T6", known_good=44, kind="candidates", ch="H"),
    "senate_candidates": dict(chart_id="AMHcn", known_good=56, kind="candidates", ch="S"),
}

FEC_BASE_URL = "https://api.open.fec.gov/v1/candidates/totals/"
USER_AGENT = "impact-refresh/1.0 (+https://github.com/; static site data refresh script)"
HTTP_TIMEOUT = 25
MAX_VERSION_PROBE = 250  # safety cap so a probing loop can never run forever


# ---------------------------------------------------------------------------
# math (identical to scripts/build.py)
# ---------------------------------------------------------------------------

def phi(z):
    return math.exp(-0.5 * z * z) / math.sqrt(2 * math.pi)


def phi_inv(p):
    p = min(max(p, 1e-9), 1 - 1e-9)
    a = [-3.969683028665376e+01, 2.209460984245205e+02, -2.759285104469687e+02,
         1.383577518672690e+02, -3.066479806614716e+01, 2.506628277459239e+00]
    b = [-5.447609879822406e+01, 1.615858368580409e+02, -1.556989798598866e+02,
         6.680131188771972e+01, -1.328068155288572e+01]
    c = [-7.784894002430293e-03, -3.223964580411365e-01, -2.400758277161838e+00,
         -2.549732539343734e+00, 4.374664141464968e+00, 2.938163982698783e+00]
    d = [7.784695709041462e-03, 3.224671290700398e-01, 2.445134137142996e+00, 3.754408661907416e+00]
    pl = 0.02425
    if p < pl:
        q = math.sqrt(-2 * math.log(p))
        return (((((c[0]*q+c[1])*q+c[2])*q+c[3])*q+c[4])*q+c[5])/((((d[0]*q+d[1])*q+d[2])*q+d[3])*q+1)
    if p > 1 - pl:
        q = math.sqrt(-2 * math.log(1 - p))
        return -(((((c[0]*q+c[1])*q+c[2])*q+c[3])*q+c[4])*q+c[5])/((((d[0]*q+d[1])*q+d[2])*q+d[3])*q+1)
    q = p - .5
    r = q * q
    return (((((a[0]*r+a[1])*r+a[2])*r+a[3])*r+a[4])*r+a[5])*q/(((((b[0]*r+b[1])*r+b[2])*r+b[3])*r+b[4])*r+1)


# ---------------------------------------------------------------------------
# HTTP helpers
# ---------------------------------------------------------------------------

def http_get(url, timeout=HTTP_TIMEOUT):
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.read()


def fetch_latest_chart_csv(chart_id, known_good_v):
    """Probe https://datawrapper.dwcdn.net/{id}/{v}/dataset.csv upward from
    known_good_v until a request 404s; return (version, csv_text) for the
    newest version that succeeded. Raises if even known_good_v fails."""
    v = known_good_v
    last_good_v = None
    last_good_text = None
    while v < known_good_v + MAX_VERSION_PROBE:
        url = "https://datawrapper.dwcdn.net/%s/%d/dataset.csv" % (chart_id, v)
        try:
            raw = http_get(url)
        except urllib.error.HTTPError as e:
            if e.code == 404:
                break
            if last_good_text is not None:
                # transient error on a newer version; keep what we have
                break
            raise RuntimeError("chart %s: HTTP %s fetching known-good version %d" % (chart_id, e.code, v))
        except urllib.error.URLError as e:
            if last_good_text is not None:
                break
            raise RuntimeError("chart %s: network error fetching known-good version %d: %s" % (chart_id, v, e))
        last_good_v = v
        last_good_text = raw.decode("utf-8-sig", errors="replace")
        v += 1
    if last_good_text is None:
        raise RuntimeError("chart %s: known-good version %d itself failed; cannot proceed" % (chart_id, known_good_v))
    return last_good_v, last_good_text


def rows_from_csv_text(text):
    return list(csv.DictReader(io.StringIO(text)))


# ---------------------------------------------------------------------------
# party / vote-share helpers
# ---------------------------------------------------------------------------

def party_bucket(raw):
    p = (raw or "").strip().upper()
    if p.startswith("D"):
        return "D"
    if p.startswith("R"):
        return "R"
    return "I"


def as_frac(x):
    """Normalize a win probability to a 0-1 fraction whether the source gave
    it as 0-1 or 0-100."""
    v = float(x)
    return v / 100.0 if v > 1.5 else v


def as_pct_points(x):
    """Normalize a vote share to percentage points (0-100) whether the
    source gave it as 0-1 or 0-100."""
    v = float(x)
    return v * 100.0 if v <= 1.5 else v


def norm_last_name(raw):
    s = raw or ""
    s = unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode("ascii")
    s = s.upper()
    s = re.sub(r"\b(JR|SR|II|III|IV)\b\.?", "", s)
    s = re.sub(r"[^A-Z]", "", s)
    return s


def fec_last_name(fec_name):
    # FEC "name" field is typically "LAST, FIRST MIDDLE"
    if not fec_name:
        return ""
    return fec_name.split(",", 1)[0]


def race_code_from_fec(office, state, district):
    state = (state or "").strip().upper()
    if office == "S":
        return state
    d = (district or "").strip()
    try:
        dn = int(d)
    except ValueError:
        dn = 0
    if dn <= 0:
        dn = 1  # at-large House seat
    return "%s-%d" % (state, dn)


# ---------------------------------------------------------------------------
# Silver Bulletin: VPI + candidate charts -> per-race rows
# ---------------------------------------------------------------------------

def build_races():
    """Fetch the VPI + candidate charts for House and Senate independently
    (so chamber attribution is unambiguous), join them by race code, and
    reduce each race to a single kept candidate per the rules in the module
    docstring. Returns (races, fetched_chart_versions)."""
    fetched_versions = {}
    out = []
    for ch, vpi_key, cand_key in [("H", "house_vpi", "house_candidates"), ("S", "senate_vpi", "senate_candidates")]:
        vpi_cfg = CHARTS[vpi_key]
        cand_cfg = CHARTS[cand_key]

        v1, vpi_text = fetch_latest_chart_csv(vpi_cfg["chart_id"], vpi_cfg["known_good"])
        v2, cand_text = fetch_latest_chart_csv(cand_cfg["chart_id"], cand_cfg["known_good"])
        fetched_versions[vpi_key] = v1
        fetched_versions[cand_key] = v2

        vpi_by_race = {}
        for row in rows_from_csv_text(vpi_text):
            race = (row.get("district") or "").strip()
            if not race:
                continue
            vpi_by_race[race] = dict(
                tipping=float(row["tipping"]),
                vpi=float(row["vpi"]),
                elasticity=float(row["elasticity"]),
            )

        cands_by_race = {}
        for row in rows_from_csv_text(cand_text):
            race = (row.get("state_district") or "").strip()
            if not race:
                continue
            cands_by_race.setdefault(race, []).append(row)

        for race, cands in cands_by_race.items():
            vpi = vpi_by_race.get(race)
            if not vpi:
                continue
            tip = vpi["tipping"]
            if tip <= 0:
                continue

            cands_sorted = sorted(cands, key=lambda c: -as_pct_points(c.get("forecasted_vote_share") or 0))
            top2 = cands_sorted[:2]
            if len(top2) >= 2 and party_bucket(top2[0].get("candidate_party")) == "D" \
                    and party_bucket(top2[1].get("candidate_party")) == "D":
                continue  # D-vs-D: skip

            dems = [c for c in cands_sorted if party_bucket(c.get("candidate_party")) == "D"]
            if dems:
                chosen = dems[0]
            else:
                indeps = [c for c in cands_sorted if party_bucket(c.get("candidate_party")) == "I"]
                if indeps:
                    chosen = indeps[0]
                else:
                    continue  # R-vs-R: skip

            p = as_frac(chosen.get("win_probability"))
            el = vpi["elasticity"]
            z = phi_inv(p)
            sig = SIG[ch] * el
            invN = vpi["vpi"] / tip

            if len(top2) >= 2:
                leader, second = top2[0], top2[1]
                margin = as_pct_points(leader.get("forecasted_vote_share") or 0) - \
                    as_pct_points(second.get("forecasted_vote_share") or 0)
                party = party_bucket(leader.get("candidate_party"))
            else:
                margin = 0.0
                party = party_bucket(chosen.get("candidate_party"))

            rating = (chosen.get("race_rating") or "").strip()
            if not rating:
                rating = "Toss-up" if 0.4 < p < 0.6 else ""

            out.append(dict(
                race=race, ch=ch,
                name=(chosen.get("candidate_last_name") or "").strip(),
                party=party,
                rating=rating,
                tip=tip, vpi=vpi["vpi"], el=el, p=p,
                margin=margin,
                a=invN * phi(z) / sig,
                b=vpi["vpi"],
            ))
    return out, fetched_versions


# ---------------------------------------------------------------------------
# FEC money
# ---------------------------------------------------------------------------

def fetch_fec_totals(office, api_key):
    """Page through /v1/candidates/totals/ for one office (H or S), party DEM,
    election_year=2026, min_receipts=75000. Returns a list of result dicts."""
    results = []
    page = 1
    while True:
        params = dict(
            api_key=api_key,
            office=office,
            party="DEM",
            election_year=2026,
            min_receipts=75000,
            per_page=100,
            sort="-receipts",
            page=page,
        )
        url = FEC_BASE_URL + "?" + urllib.parse.urlencode(params)
        raw = http_get(url)
        payload = json.loads(raw.decode("utf-8"))
        page_results = payload.get("results") or []
        results.extend(page_results)
        pagination = payload.get("pagination") or {}
        total_pages = pagination.get("pages")
        if not page_results:
            break
        if total_pages is not None and page >= total_pages:
            break
        if total_pages is None and len(page_results) < params["per_page"]:
            break
        page += 1
        time.sleep(0.2)  # be polite, especially on DEMO_KEY's tight rate limit
    return results


def fec_field(rec, *names, default=None):
    for n in names:
        if n in rec and rec[n] is not None:
            return rec[n]
    return default


def build_fec_index(api_key):
    """Returns dict: race_code -> list of FEC candidate-totals records
    (each augmented with normalized last_name/receipts/coh/cov)."""
    by_race = {}
    for office in ("H", "S"):
        for rec in fetch_fec_totals(office, api_key):
            state = fec_field(rec, "state")
            district = fec_field(rec, "district", default="00")
            race = race_code_from_fec(office, state, district)
            receipts = float(fec_field(rec, "receipts", default=0) or 0)
            coh = float(fec_field(rec, "cash_on_hand_end_period", "last_cash_on_hand_end_period", default=0) or 0)
            cov = fec_field(rec, "coverage_end_date", "last_report_date", default="") or ""
            cov = str(cov)[:10]  # YYYY-MM-DD if present
            name = fec_field(rec, "name", "candidate_name", default="") or ""
            by_race.setdefault(race, []).append(dict(
                receipts=receipts, coh=coh, cov=cov,
                last_name_norm=norm_last_name(fec_last_name(name)),
            ))
    return by_race


def match_money(race, dem_last_name, fec_index, prev_money_by_race):
    cands = fec_index.get(race) if fec_index is not None else None
    if cands:
        target = norm_last_name(dem_last_name)
        for c in cands:
            if c["last_name_norm"] == target:
                return dict(receipts=c["receipts"], coh=c["coh"], cov=c["cov"], match="name")
        best = max(cands, key=lambda c: c["receipts"])
        return dict(receipts=best["receipts"], coh=best["coh"], cov=best["cov"], match="top$")

    # No FEC candidates in this race (or FEC pull failed): fall back to
    # whatever this race had in the previous data.json, if anything.
    prev = (prev_money_by_race or {}).get(race)
    if prev:
        return dict(receipts=prev.get("receipts", 0.0), coh=prev.get("coh", 0.0),
                     cov=prev.get("cov", ""), match=prev.get("match", "none"))
    return dict(receipts=0.0, coh=0.0, cov="", match="none")


# ---------------------------------------------------------------------------
# cost index (static, doesn't change daily)
# ---------------------------------------------------------------------------

def load_cost_index():
    path = os.path.join(BASE, "cost_index.csv")
    cost = {}
    if os.path.exists(path):
        with open(path) as f:
            for row in csv.DictReader(f):
                cost[row["race"]] = float(row["costidx"])
    return cost


def load_prev_data_json():
    if os.path.exists(DATA_JSON):
        try:
            with open(DATA_JSON) as f:
                prev = json.load(f)
            return {r["race"]: r for r in prev.get("races", [])}
        except (json.JSONDecodeError, OSError, KeyError):
            return {}
    return {}


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main():
    api_key = os.environ.get("FEC_API_KEY", "").strip() or "DEMO_KEY"

    # 1) Silver Bulletin forecast data. Load-bearing: fail loudly if this fails.
    try:
        races, chart_versions = build_races()
    except Exception as e:
        print("FATAL: could not fetch/parse Silver Bulletin forecast data: %s" % e, file=sys.stderr)
        sys.exit(1)

    if not races:
        print("FATAL: Silver Bulletin data fetched but produced zero usable races", file=sys.stderr)
        sys.exit(1)

    print("fetched chart versions: %s" % chart_versions)

    prev_by_race = load_prev_data_json()

    # 2) FEC money. Best-effort: on failure, reuse previous data.json money fields.
    fec_index = None
    try:
        fec_index = build_fec_index(api_key)
        print("FEC: matched money data for %d races" % len(fec_index))
    except Exception as e:
        print("WARNING: FEC pull failed (%s); reusing previous data.json money fields where available" % e,
              file=sys.stderr)
        fec_index = None

    cost_idx = load_cost_index()

    for r in races:
        code = r["race"]
        m = match_money(code, r["name"], fec_index, prev_by_race)
        receipts = m["receipts"] or 0.0
        if receipts <= 0:
            receipts = MONEY_FLOOR
        coh = max(m["coh"] or 0.0, 0.0)
        cov = m["cov"] or ""

        if cov:
            try:
                cd = datetime.date(*map(int, cov.split("-")))
                months_in = max((cd - CYCLE_START).days / 30.44, 1.0)
                months_left = max((ELECTION - cd).days / 30.44, 0.0)
            except (ValueError, TypeError):
                months_in, months_left = 20.0, 2.0
        else:
            months_in, months_left = 20.0, 2.0
        rate = receipts / months_in

        r["cost"] = cost_idx.get(code, 8.0)
        r["receipts"] = receipts
        r["coh"] = coh
        r["proj"] = coh + rate * months_left
        r["rate"] = rate
        r["cov"] = cov
        r["match"] = m["match"]

    meta = dict(
        forecast_date=datetime.date.today().isoformat(),
        built=datetime.date.today().isoformat(),
        n=len(races),
        sigma=SIG,
        defaults=DEFAULTS,
        chart_versions=chart_versions,
    )

    os.makedirs(SITE, exist_ok=True)
    with open(DATA_JSON, "w") as f:
        json.dump(dict(meta=meta, races=races), f, separators=(",", ":"))

    print("wrote %d races to %s" % (len(races), DATA_JSON))


if __name__ == "__main__":
    main()
