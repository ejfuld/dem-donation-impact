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
    a division by zero) - it stays in the data with calc=False and a=b=None
    rather than being silently dropped (b = a * tipping is equally undefined
    when a is), since every money-related field is still perfectly
    well-defined for it.

Failure policy:
  - Silver Bulletin data (the forecast itself) is load-bearing. If it cannot
    be fetched, this script fails loudly (non-zero exit) rather than writing
    stale or partial data.
  - FEC candidate-totals money data is best-effort. If the FEC pull fails
    outright, we fall back to whatever money fields
    (receipts/coh/proj/rate/cov/match) already exist for that race in the
    previous site/data.json, so the site keeps working (with a floor value)
    rather than breaking the whole refresh.
  - FEC schedule_e (outside/independent-expenditure) money is best-effort
    too, and tracked separately from the candidate-totals pull above: if it
    fails outright, every race's outside_support/outside_oppose/
    outside_total just default to 0.0 rather than failing the run.
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
# $ per unit of the `reach` index (one impression to every voter in the
# race), derived as ~$0.02/impression x ~250k median House-district
# turnout. Converts the theta/reach price factor into a dollar figure so
# money can be expressed as "impression passes" (see the scoring section).
K_DOLLARS_PER_REACH = 5000.0

# Fixed model constant, deliberately NOT user-tunable: every campaign is
# treated as already having reached its electorate this many times before
# any donation. It only exists to keep the marginal value of the first
# dollar finite; it is a fudge factor with no empirical grounding, so it is
# not exposed as a degree of freedom.
PRIOR_REACH = 1.0

# Manual money overrides: race code -> hand-entered figures used instead of
# the FEC match, for cases where FEC data is known to be wrong or missing
# (e.g. a late-nominated replacement candidate whose committee hasn't filed
# yet). General mechanism - add an entry here whenever this recurs.
OVERRIDES = {
    # race code -> manual money figures used INSTEAD of the FEC match.
    # Only add an entry when FEC data is known to be wrong or missing.
    "ME": dict(
        receipts=3_000_000.0,
        coh=2_500_000.0,
        proj=6_000_000.0,
        note="FEC shows $0 because Jackson's committee has not filed since his July "
             "nomination (Q3 report due Oct 15). Press reporting: $1M+ raised by Jul 22, "
             "plus $2M in the days after the nomination. Figures here are an estimate.",
        source="https://spectrumlocalnews.com/me/maine/news/2026/07/27/maine-senate-race",
    ),
}

DEFAULTS = dict(c_house=40.0, senate_mult=0.75, sen_val=13.05, eta=0.5, theta=0.40, money="proj",
                outside_mult=0.35)

# Datawrapper chart ids + a known-good version to start probing upward from.
CHARTS = {
    "house_vpi": dict(chart_id="1Ixth", known_good=42, kind="vpi", ch="H"),
    "senate_vpi": dict(chart_id="mrCsL", known_good=45, kind="vpi", ch="S"),
    "house_candidates": dict(chart_id="NX4T6", known_good=44, kind="candidates", ch="H"),
    "senate_candidates": dict(chart_id="AMHcn", known_good=56, kind="candidates", ch="S"),
}

FEC_BASE_URL = "https://api.open.fec.gov/v1/candidates/totals/"
FEC_SCHEDULE_E_URL = "https://api.open.fec.gov/v1/schedules/schedule_e/by_candidate/"
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

    Returns (races, fetched_chart_versions, excluded, chosen_party) where
    excluded is {"dem_only": [race, ...], "rep_only": [race, ...]} and
    chosen_party is race_code -> "D"/"I", the party bucket of the race's own
    Democratic-aligned candidate (used only internally by match_money()'s
    tier 5 - it is not part of the race dict / data.json schema).
    """
    fetched_versions = {}
    out = []
    excluded = {"dem_only": [], "rep_only": []}
    chosen_party = {}
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
            chosen_party[race] = "D" if dems else "I"

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
            # it uncalculated rather than fake a number. `b` (oc P(one vote
            # flips the chamber)) is an independence decomposition, not
            # Silver's raw VPI directly: P(one vote flips the chamber) =
            # P(one vote flips the seat) x P(this seat is the tipping point)
            # = a * tipping. That guarantees b <= a (tipping is a
            # probability) and removes the unknown scaling constant that
            # using vpi directly left between a and b. `vpi` is still
            # carried on the race dict for reference - it must not drive
            # scoring any more. Identical logic lives in scripts/build.py -
            # keep the two in sync.
            if tip <= 0:
                a = None
                b = None
                N = None
                calc = False
            else:
                z = phi_inv(p)
                sig = SIG[ch] * el
                invN = vpi["vpi"] / tip
                a = invN * phi(z) / sig
                b = a * tip
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
                a=a, b=b, N=N, calc=calc,
            ))
    return out, fetched_versions, excluded, chosen_party


# ---------------------------------------------------------------------------
# FEC money
# ---------------------------------------------------------------------------

def fetch_fec_totals(office, api_key):
    """Page through /v1/candidates/totals/ for one office (H or S), ALL
    parties, election_year=2026 - every declared candidate, Democratic,
    Republican, independent or minor-party, however small (no min_receipts
    floor and no party filter), so downstream matching has the full field to
    work with. A party filter here would silently drop independent
    candidates' committees (they file with FEC as IND/UNK, never DEM) and
    leave their races permanently unmatched - see match_money()'s tier 5 for
    how the party-agnostic pull is kept from misattributing a race's money
    to the wrong candidate. Returns a list of result dicts."""
    results = []
    page = 1
    while True:
        params = dict(
            api_key=api_key,
            office=office,
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
    Each record carries normalized last_name/party/receipts/coh/cov and,
    when the API supplied them, candidate_status/is_active_candidate. `party`
    is bucketed D/R/I the same way Silver's candidate_party is (see
    party_bucket) - now that fetch_fec_totals() pulls every party, tier 5 of
    match_money() needs it to avoid handing a race's money to the wrong
    party's committee."""
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
            party = fec_field(rec, "party", "party_full", default="") or """
            cand = dict(
                receipts=receipts, coh=coh, cov=cov,
                last_name_norm=norm_last_name(fec_last_name(name)),
                party=party_bucket(party),
                candidate_status=fec_field(rec, "candidate_status", default=None),
                is_active_candidate=fec_field(rec, "is_active_candidate", default=None),
                candidate_id=(fec_field(rec, "candidate_id", default="") or ""),
            )
            fec_by_race.setdefault(race, []).append(cand)
            fec_by_state.setdefault((state, office), []).append(cand)
    return fec_by_race, fec_by_state


def match_money(race, ch, dem_last_name, chosen_party, fec_by_race, fec_by_state):
    """6-tier matching cascade against already-fetched FEC data (see module
    docstring). Assumes fec_by_race/fec_by_state are real - possibly with
    zero candidates for this particular race. Callers handle "the whole FEC
    pull failed" separately (see main()).

    `chosen_party` is the party bucket ("D" or "I") of the race's own
    Democratic-aligned candidate, as decided in build_races(). It only
    matters for tier 5 (see below) - tiers 1-4 match on name alone, which is
    exactly what lets an independent (NE/Osborn, SD/Bengs, ID/Achilles, ...)
    match their own FEC committee now that fetch_fec_totals() no longer
    filters to party=DEM."""
    target = norm_last_name(dem_last_name)
    state = race if ch == "S" else race.split("-")[0]

    same = fec_by_race.get(race) or []

    if target:
        # tier 1: exact normalized last-name match, same state+district
        exact = [c for c in same if c["last_name_norm"] == target]
        if exact:
            c = best_candidate(exact)
            return dict(receipts=c["receipts"], coh=c["coh"], cov=c["cov"], match="name",
                        candidate_id=c["candidate_id"])

        # tier 2: substring match either direction, same state+district
        sub = [c for c in same if c["last_name_norm"]
               and (target in c["last_name_norm"] or c["last_name_norm"] in target)]
        if sub:
            c = best_candidate(sub)
            return dict(receipts=c["receipts"], coh=c["coh"], cov=c["cov"], match="fuzzy",
                        candidate_id=c["candidate_id"])

        # tier 3: edit distance <= 2, same state+district
        near = [c for c in same if c["last_name_norm"] and levenshtein(target, c["last_name_norm"]) <= 2]
        if near:
            c = best_candidate(near)
            return dict(receipts=c["receipts"], coh=c["coh"], cov=c["cov"], match="edit",
                        candidate_id=c["candidate_id"])

        # tier 4: exact match anywhere in the same state, ignoring district
        # (catches redistricting, where the FEC record still carries the old
        # district number) - House only, Senate has no district to ignore.
        if ch == "H":
            state_cands = fec_by_state.get((state, "H")) or []
            state_exact = [c for c in state_cands if c["last_name_norm"] == target]
            if state_exact:
                c = best_candidate(state_exact)
                return dict(receipts=c["receipts"], coh=c["coh"], cov=c["cov"], match="state",
                        candidate_id=c["candidate_id"])

    # tier 5: give up on name-matching, just pick someone in this race.
    # `same` can now hold every party (fetch_fec_totals no longer filters to
    # party=DEM), so "highest receipts" alone would happily hand a
    # Democratic-aligned candidate's row the Republican opponent's money.
    # Reproduce the old (DEM-only-pull) behavior by preferring a Democrat
    # when one is on the ballot; only when the race itself has no Democrat -
    # its own chosen candidate is an independent - fall back to the closest
    # name match of any party instead of blindly taking top receipts.
    if same:
        dem_same = [c for c in same if c["party"] == "D"]
        if dem_same:
            c = best_candidate(dem_same)
            return dict(receipts=c["receipts"], coh=c["coh"], cov=c["cov"], match="top$",
                        candidate_id=c["candidate_id"])

        if chosen_party == "I" and target:
            named = [c for c in same if c["last_name_norm"]]
            if named:
                c = min(named, key=lambda c: levenshtein(target, c["last_name_norm"]))
                return dict(receipts=c["receipts"], coh=c["coh"], cov=c["cov"], match="top$",
                            candidate_id=c["candidate_id"])

        c = best_candidate(same)
        return dict(receipts=c["receipts"], coh=c["coh"], cov=c["cov"], match="top$",
                    candidate_id=c["candidate_id"])

    # tier 6: nothing
    return dict(receipts=0.0, coh=0.0, cov="", match="none", candidate_id="")


def find_opponent_id(race, chosen_party_bucket, fec_by_race):
    """This race's main opponent, for the outside-money lookup below: the
    highest-receipts FEC candidate in the same state+district whose party
    bucket differs from the chosen Democratic-or-independent candidate's
    (`chosen_party_bucket`, "D" or "I" - see build_races()). Returns the
    opponent's FEC candidate_id, or None if no such candidate is present in
    the FEC data for this race."""
    same = fec_by_race.get(race) or []
    opp_candidates = [c for c in same if c["party"] != chosen_party_bucket and c.get("candidate_id")]
    if not opp_candidates:
        return None
    c = max(opp_candidates, key=lambda c: c.get("receipts", 0.0))
    return c["candidate_id"]


# ---------------------------------------------------------------------------
# FEC independent expenditures (schedule_e): outside/IE money, best-effort
# ---------------------------------------------------------------------------

def fetch_schedule_e_totals(office, api_key):
    """Page through /v1/schedules/schedule_e/by_candidate/ for one office (H
    or S): independent-expenditure totals aggregated by candidate_id +
    support_oppose_indicator, for cycle=2026 with election_full=true (the
    whole two-year cycle, not just the current filing period). Queried in
    bulk (all candidates for the office in one paged pull) rather than per
    candidate. Returns a list of result dicts, each expected to carry
    candidate_id, support_oppose_indicator ("S" or "O") and a total dollar
    figure."""
    results = []
    page = 1
    while True:
        params = dict(
            api_key=api_key,
            cycle=2026,
            office=office,
            election_full="true",
            per_page=100,
            page=page,
        )
        url = FEC_SCHEDULE_E_URL + "?" + urllib.parse.urlencode(params)
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


def build_outside_index(api_key):
    """(candidate_id, "S"|"O") -> total independent-expenditure dollars,
    pulled in bulk across House + Senate, cycle=2026, election_full=true.
    Best-effort: callers decide what to do if the whole pull fails (see
    main()) - this data is unlike the Silver Bulletin forecast, which is
    load-bearing."""
    lookup = {}
    for office in ("H", "S"):
        for rec in fetch_schedule_e_totals(office, api_key):
            cid = (rec.get("candidate_id") or "").strip()
            ind = (rec.get("support_oppose_indicator") or "").strip().upper()
            if not cid or ind not in ("S", "O"):
                continue
            total = float(rec.get("total") or 0.0)
            key = (cid, ind)
            lookup[key] = lookup.get(key, 0.0) + total
    return lookup


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
        races, chart_versions, excluded, chosen_party_by_race = build_races()
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

    # 3) FEC independent expenditures (schedule_e). Best-effort like the
    # money pull above, but tracked separately: it's fine for this to fail
    # even when the candidate-totals pull above succeeded. On total failure,
    # every race's outside_* fields default to 0.0 rather than the run
    # failing - this is best-effort, unlike the Silver Bulletin data.
    outside_lookup = None
    try:
        outside_lookup = build_outside_index(api_key)
        print("FEC: pulled independent-expenditure totals covering %d (candidate,S/O) pairs" %
              len(outside_lookup))
    except Exception as e:
        print("WARNING: FEC schedule_e (outside money) pull failed (%s); outside_* fields default to 0.0" % e,
              file=sys.stderr)
        outside_lookup = None

    cost_idx = load_cost_index()

    match_counts = {"name": 0, "fuzzy": 0, "edit": 0, "state": 0, "top$": 0, "none": 0}

    for r in races:
        code = r["race"]
        prev = prev_by_race.get(code) or {}
        if fec_by_race is not None:
            m = match_money(code, r["ch"], r["name"], chosen_party_by_race.get(code, "D"),
                             fec_by_race, fec_by_state)
            cand_id = m.get("candidate_id") or None
            opp_id = find_opponent_id(code, chosen_party_by_race.get(code, "D"), fec_by_race)
        else:
            m = dict(receipts=prev.get("receipts", 0.0), coh=prev.get("coh", 0.0),
                      cov=prev.get("cov", ""), match=prev.get("match", "none"))
            # candidate-totals pull failed outright, so there's no fresh FEC
            # candidate_id to resolve either side from - fall back to
            # whatever this race's opp_id was on the last successful run.
            cand_id = None
            opp_id = prev.get("opp_id")

        receipts = m["receipts"] or 0.0
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

        # --- manual money overrides (see OVERRIDES near the top) ---
        # Keyed by the exact `race` code, so this lookup works unchanged for
        # both Senate ("ME") and House ("PA-10") race codes.
        ov = OVERRIDES.get(code)
        if ov:
            r["receipts"] = ov["receipts"]
            r["coh"] = ov["coh"]
            r["proj"] = ov["proj"]
            r["match"] = "manual"
            r["override"] = True
            r["note"] = ov["note"]
            r["source"] = ov["source"]
        else:
            r["override"] = False

        r["opp_id"] = opp_id

        # outside/independent-expenditure money that helps this race's
        # Democratic-aligned candidate: IE dollars SUPPORTING them directly,
        # plus IE dollars OPPOSING their main opponent. Both default to 0.0
        # when unknown (no cand_id/opp_id to key on, or the schedule_e pull
        # failed entirely) - never None, same as every other money field.
        if outside_lookup is not None:
            outside_support = outside_lookup.get((cand_id, "S"), 0.0) if cand_id else 0.0
            outside_oppose = outside_lookup.get((opp_id, "O"), 0.0) if opp_id else 0.0
        else:
            outside_support = 0.0
            outside_oppose = 0.0
        r["outside_support"] = outside_support
        r["outside_oppose"] = outside_oppose
        r["outside_total"] = outside_support + outside_oppose

        match_counts[r["match"]] = match_counts.get(r["match"], 0) + 1

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
    overridden_races = sorted(r["race"] for r in races if r.get("override"))

    # money_eff: the money the campaign effectively commands - its own
    # selected money figure, plus outside/IE spending that helps it,
    # discounted by outside_mult (candidates get the statutory lowest unit
    # rate for broadcast, outside groups don't - see build.py for the full
    # note). Computed for every race, calc or not, same as proj/receipts/coh.
    for r in races:
        r["money_eff"] = r[DEFAULTS["money"]] + DEFAULTS["outside_mult"] * r["outside_total"]

    # ---------------------------------------------------------------------
    # scoring: identical to scripts/build.py - see that file for the full
    # derivation and keep the two in sync. anchor/total_races/mean_raw are
    # baked into meta so the front end uses the exact same numbers rather
    # than recomputing them independently.
    # ---------------------------------------------------------------------
    # theta anchor: the MEAN reach cost across House races that could be
    # scored, replacing the old fixed "fully targetable" cost of 1.0.
    house_calc_reach = [r["reach"] for r in races if r["ch"] == "H" and r["calc"]]
    anchor = sum(house_calc_reach) / len(house_calc_reach) if house_calc_reach else 0.0

    total_races = len(races) + len(excluded_all)   # every race on the board, scored or not

    raw_by_race = {}
    for r in races:
        if r["calc"]:
            c_eff = DEFAULTS["c_house"] * DEFAULTS["senate_mult"] if r["ch"] == "S" else DEFAULTS["c_house"]
            w = DEFAULTS["sen_val"] if r["ch"] == "S" else 1.0
            V = c_eff * r["b"] + w * r["a"]
            # P_dollars: dollar cost of one full "impression pass" (touching
            # every voter in the race once), theta/reach-blended same as
            # before, just converted from the `reach` index into dollars via K.
            P_eff = DEFAULTS["theta"] * anchor + (1 - DEFAULTS["theta"]) * r["reach"]
            p_dollars = P_eff * K_DOLLARS_PER_REACH
            # passes: how many impression passes the campaign's money buys,
            # out of money_eff (its own money plus discounted outside money)
            # rather than the raw money field alone. No money floor needed
            # any more: at money==0, passes==0 and (prior_reach + passes)
            # **-eta is still finite (see build.py).
            passes = r["money_eff"] / p_dollars
            # elasticity enters twice: once widening sigma (inside `a`,
            # computed above in build_races()), once again here as an
            # ease-of-persuasion multiplier on raw impact. Nrel: a dollar
            # buys a fixed fraction of reach, and that fraction touches more
            # real voters in a larger electorate - see build.py for the full
            # derivation of both this and the CRRA (prior_reach + passes)
            # shape, which replaces the old money**-eta * P**(eta-1) form
            # (equivalent when passes >> prior_reach, finite at money == 0).
            raw_by_race[r["race"]] = (
                V * r["el"] * r["Nrel"] * (PRIOR_REACH + passes) ** -DEFAULTS["eta"] / p_dollars
            )
            r["p_dollars"] = p_dollars
            r["passes"] = passes
        else:
            raw_by_race[r["race"]] = 0.0   # calc==False races score 0 but still count in the denominator
            r["p_dollars"] = None
            r["passes"] = None

    # mean (not max) raw score over EVERY race on the board: races with
    # calc == False contribute 0 to the sum, and excluded races contribute 0
    # too (they aren't in raw_by_race at all, but they are counted in
    # total_races) - so the mean race, not the top race, scores impact == 100.
    mean_raw = sum(raw_by_race.values()) / total_races

    outside_vals = [r["outside_total"] for r in races]
    outside_totals = dict(races_with_outside=sum(1 for v in outside_vals if v > 0),
                           sum=sum(outside_vals))

    meta = dict(
        forecast_date=datetime.date.today().isoformat(),
        built=datetime.date.today().isoformat(),
        n=len(races),
        n_calc=sum(1 for r in races if r["calc"]),
        sigma=SIG,
        k_dollars_per_reach=K_DOLLARS_PER_REACH,
        defaults=DEFAULTS,
        anchor=anchor, total_races=total_races, mean_raw=mean_raw, prior_reach=PRIOR_REACH,
        chart_versions=chart_versions,
        excluded=dict(count=len(excluded_all), dem_only=len(excluded["dem_only"]),
                      rep_only=len(excluded["rep_only"]), races=excluded_all),
        match_counts=match_counts,
        overrides=overridden_races,
        outside_totals=outside_totals,
    )

    os.makedirs(SITE, exist_ok=True)
    with open(DATA_JSON, "w") as f:
        json.dump(dict(meta=meta, races=races), f, separators=(",", ":"))

    print("wrote %d races (%d calc) to %s" % (len(races), meta["n_calc"], DATA_JSON))
    print("excluded %d races: dem_only=%d rep_only=%d" %
          (meta["excluded"]["count"], meta["excluded"]["dem_only"], meta["excluded"]["rep_only"]))
    print("FEC match tiers: %s" % match_counts)
    print("outside totals: %s" % outside_totals)


if __name__ == "__main__":
    main()
