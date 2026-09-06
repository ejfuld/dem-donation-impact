#!/usr/bin/env python3
"""Daily refresh: re-pull live Silver Bulletin + FEC inputs and regenerate site/data.json.

Standard library only (urllib, csv, json). Designed to run unattended from
GitHub Actions. Reuses the exact math from scripts/build.py so the output
shape and field semantics never drift from what site/index.html expects.

Race selection:
  - A race is KEPT only when it has at least one Democratic-or-independent
    candidate AND at least one Republican candidate. Everything else
    (D-vs-D top-two races, R-vs-R top-two races, or a plain unopposed seat)
    is dropped entirely and tallied into meta["excluded"].
  - A kept race with tipping <= 0 has an undefined `a` (a = vpi/tipping,
    a division by zero) - it stays in the data with calc=False and a=None
    rather than being silently dropped, since b (=vpi) and every
    money-related field are still perfectly well-defined for it.

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
import statistics as _st
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
MONEY_FLOOR = 1_000_000.0

DEFAULTS = dict(c_house=25.0, senate_mult=0.75, sen_val=13.05, eta=0.72, theta=0.40, money="proj")

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
# `why` chips: rule-based, computed purely from a race's own numbers.
# Shared logic with scripts/build.py - keep the two in sync.
# ---------------------------------------------------------------------------

def compute_why(r, top15_races):
    chips = []

    p = r["p"]
    if 0.40 <= p <= 0.60:
        chips.append("Toss-up")
    elif (0.60 < p <= 0.80) or (0.20 <= p < 0.40):
        chips.append("Competitive")
    elif (0.80 < p <= 0.93) or (0.07 <= p < 0.20):
        chips.append("Leaning")
    else:
        chips.append("Safe seat")
    if len(chips) >= 4:
        return chips[:4]

    if r["Nrel"] is not None:
        if r["Nrel"] < 0.75:
            chips.append("Small electorate")
        elif r["Nrel"] > 3.0:
            chips.append("Very large electorate")
        if len(chips) >= 4:
            return chips[:4]

    if r["reach"] is not None:
        if r["reach"] < 2.5:
            chips.append("Cheap to reach voters")
        elif r["reach"] > 15:
            chips.append("Expensive media market")
        if len(chips) >= 4:
            return chips[:4]

    proj = r["proj"]
    if proj < 1_500_000:
        chips.append("Little money raised")
    elif proj > 15_000_000:
        chips.append("Already well funded")
    if len(chips) >= 4:
        return chips[:4]

    if r["race"] in top15_races:
        chips.append("Often the decisive seat")
        if len(chips) >= 4:
            return chips[:4]

    if r["ch"] == "S":
        chips.append("Senate seat (6-year term)")

    return chips[:4]


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
    """Uppercase, accent-stripped, suffix-stripped, letters-only surname key.
    E.g. "Gluesenkamp Pérez" -> "GLUESENKAMPPEREZ", "O'Rourke" -> "OROURKE"."""
    s = raw or ""
    s = s.upper()
    s = unicodedata.normalize("NFD", s)
    s = "".join(ch for ch in s if unicodedata.category(ch) != "Mn")  # drop combining accents
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


def levenshtein(a, b):
    """Plain edit distance between two strings, no dependencies - fine for
    the short surname strings this is used on."""
    if a == b:
        return 0
    la, lb = len(a), len(b)
    if la == 0:
        return lb
    if lb == 0:
        return la
    prev = list(range(lb + 1))
    for i in range(1, la + 1):
        cur = [i] + [0] * lb
        ca = a[i - 1]
        for j in range(1, lb + 1):
            cost = 0 if ca == b[j - 1] else 1
            cur[j] = min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + cost)
        prev = cur
    return prev[lb]


def best_candidate(cands):
    """Pick among several FEC records at the same match tier: highest
    receipts wins; ties broken toward an active, currently-filed candidate
    (candidate_status == 'C' / is_active_candidate) when the API supplied
    those fields."""
    def sort_key(c):
        return (
            c.get("receipts", 0.0),
            1 if c.get("candidate_status") == "C" else 0,
            1 if c.get("is_active_candidate") else 0,
        )
    return max(cands, key=sort_key)


# ---------------------------------------------------------------------------
# Silver Bulletin: VPI + candidate charts -> per-race rows
# ---------------------------------------------------------------------------

def build_races():
    """Fetch the VPI + candidate charts for House and Senate independently
    (so chamber attribution is unambiguous), join them by race code, and
    classify each race by which parties are actually contesting it.

    A race is KEPT only when it has at least one Democratic-or-independent
    candidate AND at least one Republican candidate in Silver's candidate
    list - that's what "a two-party contest exists" means here. Everything
    else (D-vs-D top-two races, R-vs-R top-two races, or a plain unopposed
    seat) is dropped entirely and tallied into `excluded`.

    Returns (races, fetched_chart_versions, excluded) where excluded is
    {"dem_only": [race, ...], "rep_only": [race, ...]}.
    """
    fetched_versions = {}
    out = []
    excluded = {"dem_only": [], "rep_only": []}
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

            cands_sorted = sorted(cands, key=lambda c: -as_pct_points(c.get("forecasted_vote_share") or 0))

            dems = [c for c in cands_sorted if party_bucket(c.get("candidate_party")) == "D"]
            indeps = [c for c in cands_sorted if party_bucket(c.get("candidate_party")) == "I"]
            buckets = set(party_bucket(c.get("candidate_party")) for c in cands_sorted)

            # A race is contested if two or more candidates run AND they are not
            # all from the same party. An independent stands in for whichever
            # major party is absent: D-vs-I and I-vs-R are both real contests.
            # Only same-party races (CA/WA top-two D-vs-D or R-vs-R) and
            # unopposed seats are dropped.
            if len(cands_sorted) < 2 or len(buckets) < 2:
                if buckets == {"R"}:
                    excluded["rep_only"].append(race)
                else:
                    excluded["dem_only"].append(race)
                continue

            # Democratic-aligned candidate: the Democrat if one is running,
            # otherwise the strongest independent.
            chosen = dems[0] if dems else (indeps[0] if indeps else None)
            if chosen is None:
                excluded["rep_only"].append(race)
                continue

            top2 = cands_sorted[:2]
            if len(top2) >= 2:
                leader, second = top2[0], top2[1]
                margin = as_pct_points(leader.get("forecasted_vote_share") or 0) - \
                    as_pct_points(second.get("forecasted_vote_share") or 0)
                party = party_bucket(leader.get("candidate_party"))
            else:
                margin = 0.0
                party = party_bucket(chosen.get("candidate_party"))

            rating = (chosen.get("race_rating") or "").strip()

            p = as_frac(chosen.get("win_probability"))
            el = vpi["elasticity"]

            # tipping <= 0 would make invN = vpi/tipping a division by zero,
            # so `a` is genuinely undefined there - keep the race, but mark
            # it uncalculated rather than fake a number.
            if tip <= 0:
                a = None
                N = None
                calc = False
            else:
                z = phi_inv(p)
                sig = SIG[ch] * el
                invN = vpi["vpi"] / tip
                a = invN * phi(z) / sig
                N = 1.0 / invN
                calc = True

            if not rating:
                rating = "Toss-up" if 0.4 < p < 0.6 else ""

            out.append(dict(
                race=race, ch=ch,
                name=(chosen.get("candidate_last_name") or "").strip(),
                party=party,
                rating=rating,
                tip=tip, vpi=vpi["vpi"], el=el, p=p,
                margin=margin,
                a=a, b=vpi["vpi"], N=N, calc=calc,
            ))
    return out, fetched_versions, excluded


# ---------------------------------------------------------------------------
# FEC money
# ---------------------------------------------------------------------------

def fetch_fec_totals(office, api_key):
    """Page through /v1/candidates/totals/ for one office (H or S), party
    DEM, election_year=2026 - every declared Democratic candidate, however
    small (no min_receipts floor), so downstream matching has the full field
    to work with. Returns a list of result dicts."""
    results = []
    page = 1
    while True:
        params = dict(
            api_key=api_key,
            office=office,
            party="DEM",
            election_year=2026,
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
        time.sleep(0.2)  # be polite even with a real API key
    return results


def fec_field(rec, *names, default=None):
    for n in names:
        if n in rec and rec[n] is not None:
            return rec[n]
    return default


def build_fec_indexes(api_key):
    """Returns (fec_by_race, fec_by_state):
      fec_by_race: race_code -> list of FEC candidate-totals records
      fec_by_state: (state, office) -> every record for that state
        regardless of district (the redistricting fallback, tier "state")
    Each record carries normalized last_name/receipts/coh/cov and, when the
    API supplied them, candidate_status/is_active_candidate."""
    fec_by_race = {}
    fec_by_state = {}
    for office in ("H", "S"):
        for rec in fetch_fec_totals(office, api_key):
            state = (fec_field(rec, "state") or "").strip().upper()
            district = fec_field(rec, "district", default="00")
            race = race_code_from_fec(office, state, district)
            receipts = float(fec_field(rec, "receipts", default=0) or 0)
            coh = float(fec_field(rec, "cash_on_hand_end_period", "last_cash_on_hand_end_period", default=0) or 0)
            cov = fec_field(rec, "coverage_end_date", "last_report_date", default="") or ""
            cov = str(cov)[:10]  # YYYY-MM-DD if present
            name = fec_field(rec, "name", "candidate_name", default="") or ""
            cand = dict(
                receipts=receipts, coh=coh, cov=cov,
                last_name_norm=norm_last_name(fec_last_name(name)),
                candidate_status=fec_field(rec, "candidate_status", default=None),
                is_active_candidate=fec_field(rec, "is_active_candidate", default=None),
            )
            fec_by_race.setdefault(race, []).append(cand)
            fec_by_state.setdefault((state, office), []).append(cand)
    return fec_by_race, fec_by_state


def match_money(race, ch, dem_last_name, fec_by_race, fec_by_state):
    """6-tier matching cascade against already-fetched FEC data (see module
    docstring). Assumes fec_by_race/fec_by_state are real - possibly with
    zero candidates for this particular race. Callers handle "the whole FEC
    pull failed" separately (see main())."""
    target = norm_last_name(dem_last_name)
    state = race if ch == "S" else race.split("-")[0]

    same = fec_by_race.get(race) or []

    if target:
        # tier 1: exact normalized last-name match, same state+district
        exact = [c for c in same if c["last_name_norm"] == target]
        if exact:
            c = best_candidate(exact)
            return dict(receipts=c["receipts"], coh=c["coh"], cov=c["cov"], match="name")

        # tier 2: substring match either direction, same state+district
        sub = [c for c in same if c["last_name_norm"]
               and (target in c["last_name_norm"] or c["last_name_norm"] in target)]
        if sub:
            c = best_candidate(sub)
            return dict(receipts=c["receipts"], coh=c["coh"], cov=c["cov"], match="fuzzy")

        # tier 3: edit distance <= 2, same state+district
        near = [c for c in same if c["last_name_norm"] and levenshtein(target, c["last_name_norm"]) <= 2]
        if near:
            c = best_candidate(near)
            return dict(receipts=c["receipts"], coh=c["coh"], cov=c["cov"], match="edit")

        # tier 4: exact match anywhere in the same state, ignoring district
        # (catches redistricting, where the FEC record still carries the old
        # district number) - House only, Senate has no district to ignore.
        if ch == "H":
            state_cands = fec_by_state.get((state, "H")) or []
            state_exact = [c for c in state_cands if c["last_name_norm"] == target]
            if state_exact:
                c = best_candidate(state_exact)
                return dict(receipts=c["receipts"], coh=c["coh"], cov=c["cov"], match="state")

    # tier 5: highest-receipts Democrat in that state+district
    if same:
        c = best_candidate(same)
        return dict(receipts=c["receipts"], coh=c["coh"], cov=c["cov"], match="top$")

    # tier 6: nothing
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
        races, chart_versions, excluded = build_races()
    except Exception as e:
        print("FATAL: could not fetch/parse Silver Bulletin forecast data: %s" % e, file=sys.stderr)
        sys.exit(1)

    if not races:
        print("FATAL: Silver Bulletin data fetched but produced zero usable races", file=sys.stderr)
        sys.exit(1)

    print("fetched chart versions: %s" % chart_versions)

    prev_by_race = load_prev_data_json()

    # 2) FEC money. Best-effort: on total failure, reuse previous data.json
    # money fields for every race. On success, each race runs the 6-tier
    # matching cascade against the freshly pulled FEC data (which may still
    # come up empty for an individual race -> match="none").
    fec_by_race = None
    fec_by_state = None
    try:
        fec_by_race, fec_by_state = build_fec_indexes(api_key)
        print("FEC: pulled candidate totals covering %d distinct races" % len(fec_by_race))
    except Exception as e:
        print("WARNING: FEC pull failed (%s); reusing previous data.json money fields where available" % e,
              file=sys.stderr)
        fec_by_race = None
        fec_by_state = None

    cost_idx = load_cost_index()

    match_counts = {"name": 0, "fuzzy": 0, "edit": 0, "state": 0, "top$": 0, "none": 0}

    for r in races:
        code = r["race"]
        if fec_by_race is not None:
            m = match_money(code, r["ch"], r["name"], fec_by_race, fec_by_state)
        else:
            prev = prev_by_race.get(code) or {}
            m = dict(receipts=prev.get("receipts", 0.0), coh=prev.get("coh", 0.0),
                      cov=prev.get("cov", ""), match=prev.get("match", "none"))

        match_counts[m["match"]] = match_counts.get(m["match"], 0) + 1

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

    # electorate size / reach cost, same formula as build.py: median House N == 1
    house_Ns = [r["N"] for r in races if r["ch"] == "H" and r["N"] is not None]
    med_N = _st.median(house_Ns) if house_Ns else 1.0
    for r in races:
        if r["N"] is not None:
            r["Nrel"] = r["N"] / med_N
            r["reach"] = r["cost"] * r["Nrel"]
        else:
            r["Nrel"] = None
            r["reach"] = None

    top15 = set(r["race"] for r in sorted(races, key=lambda x: -x["tip"])[:15])
    for r in races:
        r["why"] = compute_why(r, top15)

    excluded_all = sorted(excluded["dem_only"] + excluded["rep_only"])
    meta = dict(
        forecast_date=datetime.date.today().isoformat(),
        built=datetime.date.today().isoformat(),
        n=len(races),
        n_calc=sum(1 for r in races if r["calc"]),
        sigma=SIG,
        money_floor=MONEY_FLOOR,
        defaults=DEFAULTS,
        chart_versions=chart_versions,
        excluded=dict(count=len(excluded_all), dem_only=len(excluded["dem_only"]),
                      rep_only=len(excluded["rep_only"]), races=excluded_all),
        match_counts=match_counts,
    )

    os.makedirs(SITE, exist_ok=True)
    with open(DATA_JSON, "w") as f:
        json.dump(dict(meta=meta, races=races), f, separators=(",", ":"))

    print("wrote %d races (%d calc) to %s" % (len(races), meta["n_calc"], DATA_JSON))
    print("excluded %d races: dem_only=%d rep_only=%d" %
          (meta["excluded"]["count"], meta["excluded"]["dem_only"], meta["excluded"]["rep_only"]))
    print("FEC match tiers: %s" % match_counts)


if __name__ == "__main__":
    main()
