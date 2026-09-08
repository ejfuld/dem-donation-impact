"""Join Silver Bulletin forecast + media-market cost index + FEC money -> data.json"""
import csv, json, math, datetime, os, statistics as _st
BASE = os.path.join(os.path.dirname(__file__), '..', 'data')
SIG = {'H': 6.65, 'S': 6.69}
ELECTION = datetime.date(2026, 11, 3)
CYCLE_START = datetime.date(2025, 1, 1)
# $ per unit of the `reach` index (one impression to every voter in the
# race), derived as ~$0.02/impression x ~250k median House-district
# turnout. Converts the theta/reach price factor into a dollar figure so
# money can be expressed as "impression passes" (see the scoring section).
K_DOLLARS_PER_REACH = 5000.0

# Fixed model constant, deliberately NOT user-tunable: every campaign is
# treated as already having reached its electorate this many times before
# any donation - standing in for the "free" reach a campaign gets without
# paying for it (ballot party label, earned media, existing name ID, party
# infrastructure). It also keeps the marginal value of the first dollar
# finite. It is a fudge factor with no rigorous empirical grounding, so it
# is not exposed as a degree of freedom; raised twice on 2026-09-08 (1.0 ->
# 10.0 -> 30.0) as the owner's own judgment call for that free reach, not a
# derived figure - see the site's methodology section for the reasoning.
PRIOR_REACH = 30.0

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
        expires="2026-10-20",
        source="https://spectrumlocalnews.com/me/maine/news/2026/07/27/maine-senate-race",
    ),
}


def active_overrides(today=None):
    """OVERRIDES minus any whose `expires` date has passed."""
    today = today or datetime.date.today()
    out = {}
    for race, ov in OVERRIDES.items():
        exp = ov.get("expires")
        if exp and datetime.date(*map(int, exp.split("-"))) < today:
            continue
        out[race] = ov
    return out



def phi(z): return math.exp(-0.5 * z * z) / math.sqrt(2 * math.pi)


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
    q = p - .5; r = q * q
    return (((((a[0]*r+a[1])*r+a[2])*r+a[3])*r+a[4])*r+a[5])*q/(((((b[0]*r+b[1])*r+b[2])*r+b[3])*r+b[4])*r+1)


def rd(f): return list(csv.DictReader(open(os.path.join(BASE, f))))


# ---------------------------------------------------------------------------
# `why` chips: rule-based, computed purely from a race's own numbers.
# Shared logic with scripts/refresh.py - keep the two in sync.
# ---------------------------------------------------------------------------

def compute_why(r, top15_races):
    chips = []

    p = r['p']
    if 0.40 <= p <= 0.60:
        chips.append('Toss-up')
    elif (0.60 < p <= 0.80) or (0.20 <= p < 0.40):
        chips.append('Competitive')
    elif (0.80 < p <= 0.93) or (0.07 <= p < 0.20):
        chips.append('Leaning')
    else:
        chips.append('Safe seat')
    if len(chips) >= 4:
        return chips[:4]

    if r['Nrel'] is not None:
        if r['Nrel'] < 0.75:
            chips.append('Small electorate')
        elif r['Nrel'] > 3.0:
            chips.append('Very large electorate')
        if len(chips) >= 4:
            return chips[:4]

    if r['reach'] is not None:
        if r['reach'] < 2.5:
            chips.append('Cheap to reach voters')
        elif r['reach'] > 15:
            chips.append('Expensive media market')
        if len(chips) >= 4:
            return chips[:4]

    proj = r['proj']
    if proj < 1_500_000:
        chips.append('Little money raised')
    elif proj > 15_000_000:
        chips.append('Already well funded')
    if len(chips) >= 4:
        return chips[:4]

    if r['race'] in top15_races:
        chips.append('Often the decisive seat')
        if len(chips) >= 4:
            return chips[:4]

    if r['ch'] == 'S':
        chips.append('Senate seat (6-year term)')

    return chips[:4]


cost = {r['race']: float(r['costidx']) for r in rd('cost_index.csv')}
money = {r['race']: r for r in rd('money_2026-09-04.csv')}
marg = {r['race']: r for r in rd('margins_2026-09-04.csv')}

# Outside / independent-expenditure money (see scripts/refresh.py for the
# live FEC schedule_e pull that produces this file day to day). No network
# in build.py, so this is read from a checked-in CSV when present; when it's
# absent (e.g. a fresh checkout before the first refresh has run) every
# race just gets outside_support == outside_oppose == outside_total == 0.0 -
# this must never fail the build.
_outside_path = os.path.join(BASE, 'outside_2026.csv')
outside = {r['race']: r for r in rd('outside_2026.csv')} if os.path.exists(_outside_path) else {}

races = []
dem_only_races = []
rep_only_races = []
for fn, ch in [('silver_house_2026-09-04.csv', 'H'), ('silver_senate_2026-09-04.csv', 'S')]:
    for r in rd(fn):
        code = r['race']
        tip = float(r['tipping'])

        # This static snapshot tracks a single Democratic-or-independent
        # candidate per race (columns dem_last/dem_win) and carries no signal
        # for whether a Republican is on the ballot opposite them. A blank
        # dem_last/dem_win means the snapshot has no viable D-or-I candidate
        # to report for this race at all, so it's treated as Republican-only
        # and excluded (this reproduces every exclusion the old
        # `not r['dem_win']` filter produced, just counted/reported instead
        # of silently dropped). There is no equivalent signal here for a
        # Democrat-unopposed race, so dem_only stays empty for build.py.
        if not r['dem_win'] or not r['dem_last']:
            rep_only_races.append(code)
            continue

        p = float(r['dem_win'])
        el = float(r['elasticity'])
        vpi = float(r['vpi'])

        m = money.get(code, {})
        receipts = float(m.get('receipts') or 0)
        coh = max(float(m.get('coh') or 0), 0.0)
        cov = m.get('covend') or ''
        # monthly contribution rate, extrapolated to election day
        if cov:
            cd = datetime.date(*map(int, cov.split('-')))
            months_in = max((cd - CYCLE_START).days / 30.44, 1.0)
            months_left = max((ELECTION - cd).days / 30.44, 0.0)
        else:
            months_in, months_left = 20.0, 2.0
        rate = receipts / months_in

        # tipping == 0 would make invN = vpi/tipping a division by zero, so
        # `a` (oc P(one vote flips the seat)) is genuinely undefined there -
        # keep the race, but mark it uncalculated rather than fake a number.
        # `b` (oc P(one vote flips the chamber)) is then an independence
        # decomposition, not Silver's raw VPI directly: P(one vote flips the
        # chamber) = P(one vote flips the seat) x P(this seat is the tipping
        # point) = a * tipping. That guarantees b <= a (tipping is a
        # probability, so tipping <= 1) and removes the unknown scaling
        # constant that using vpi directly left between a and b. `vpi` is
        # still carried on the race dict below for reference - it must not
        # drive scoring any more.
        if tip <= 0:
            a = None
            b = None
            N = None
            calc = False
        else:
            z = phi_inv(p)
            sig = SIG[ch] * el
            invN = vpi / tip
            a = invN * phi(z) / sig
            b = a * tip
            N = 1.0 / invN
            calc = True

        ov_row = outside.get(code, {})
        outside_support = float(ov_row.get('outside_support') or 0.0)
        outside_oppose = float(ov_row.get('outside_oppose') or 0.0)

        races.append(dict(
            race=code, ch=ch, name=r['dem_last'], party=marg.get(code, {}).get('party', 'D'),
            rating=r['rating'] or ('Toss-up' if 0.4 < p < 0.6 else ''),
            tip=tip, vpi=vpi, el=el, p=p,
            margin=float(marg.get(code, {}).get('margin') or 0),
            a=a,                             # oc P(one vote flips the seat)
            b=b,                             # oc P(one vote flips the chamber) = a * tip
            cost=cost.get(code, 8.0),        # media-market overspill factor (per constituent)
            N=N,                             # oc size of the electorate
            receipts=receipts, coh=coh,
            proj=coh + rate * months_left,   # cash on hand + extrapolated contributions
            rate=rate, cov=cov,
            match=m.get('match', 'none'),
            calc=calc,
            # opp_id: build.py has no network / per-candidate FEC ids to
            # resolve a main opponent from, unlike refresh.py - always None
            # here, kept only so the two scripts stay schema-identical.
            opp_id=None,
            outside_support=outside_support, outside_oppose=outside_oppose,
            outside_total=outside_support + outside_oppose,
            Nrel=None, reach=None))          # filled in below once the House median N is known

        # --- manual money overrides (see OVERRIDES near the top) ---
        # Keyed by the exact `race` code, so this lookup works unchanged for
        # both Senate ("ME") and House ("PA-10") race codes.
        rec = races[-1]
        ov = active_overrides().get(code)
        if ov:
            rec['receipts'] = ov['receipts']
            rec['coh'] = ov['coh']
            rec['proj'] = ov['proj']
            rec['match'] = 'manual'
            rec['override'] = True
            rec['note'] = ov['note']
            rec['source'] = ov['source']
        else:
            rec['override'] = False

# --- reach cost: price of reaching a fixed share (say 1%) of THIS electorate ---
# cost[] is price per constituent impression (media-market overspill).
# Reaching 1% of the electorate costs that times the size of the electorate.
_house_Ns = [r['N'] for r in races if r['ch'] == 'H' and r['N'] is not None]
_med = _st.median(_house_Ns)
for r in races:
    if r['N'] is not None:
        r['Nrel'] = r['N'] / _med                 # electorate size, median House seat = 1
        r['reach'] = r['cost'] * r['Nrel']         # price of reaching 1% of the electorate

_top15 = set(r['race'] for r in sorted(races, key=lambda x: -x['tip'])[:15])
for r in races:
    r['why'] = compute_why(r, _top15)

# Races deliberately left UNSCORED: kept on the board with an em dash and a
# footnote rather than dropped, so a reader who goes looking finds a reason
# rather than assuming an oversight. KEEP IN SYNC with NO_SCORE in
# scripts/refresh.py - that is the copy the nightly job actually runs.
NO_SCORE = {
    'MT': dict(
        note="Montana's anti-Republican vote is split between two candidates: Alani "
             "Bankhead (D) and Seth Bodnar (I), whom Democratic Party leaders have "
             "endorsed. Bankhead has declined to withdraw. Silver's model has both "
             "running well behind the Republican, and a dollar to either one plausibly "
             "costs the other, so any single-candidate impact score here would be "
             "misleading. Left unscored until the field resolves.",
        source='https://montanafreepress.org/2026/08/10/bankhead-still-in-the-running/',
    ),
}

no_score_meta = []
for r in races:
    _ns = NO_SCORE.get(r['race'])
    if not _ns:
        r['no_score'] = False
        continue
    r['calc'] = False
    r['no_score'] = True
    r['why'] = ['Not scored - see note']
    no_score_meta.append(dict(race=r['race'], note=_ns['note'], source=_ns.get('source', '')))
no_score_meta.sort(key=lambda x: x['race'])

excluded_races = sorted(dem_only_races + rep_only_races)

match_counts = {}
for r in races:
    match_counts[r['match']] = match_counts.get(r['match'], 0) + 1
overridden_races = sorted(r['race'] for r in races if r.get('override'))

# ---------------------------------------------------------------------------
# scoring: raw marginal-impact-per-dollar at the site's default parameters.
# `anchor`/`total_races`/`mean_raw` are baked into meta so the front end (and
# anyone re-deriving `impact` from data.json) uses the exact same numbers
# rather than recomputing them independently. Identical logic lives in
# scripts/refresh.py - keep the two in sync.
# ---------------------------------------------------------------------------



DEFAULTS = dict(c_house=100.0, senate_mult=0.5, sen_val=13.05, eta=0.67, theta=0.40, money='proj',
                outside_mult=0.35)

# money_eff: the money the campaign effectively commands - its own selected
# money figure, plus outside/independent-expenditure spending that helps it,
# discounted by outside_mult because candidates get the statutory lowest
# unit rate for broadcast while outside groups do not (measured market gaps
# of 2.25x-3.5x mean an outside dollar buys roughly 29-44% of the reach a
# candidate dollar does). Computed for every race, calc or not, same as
# proj/receipts/coh - only p_dollars/passes below require calc (they need
# `reach`, which needs N).
for r in races:
    r['money_eff'] = r[DEFAULTS['money']] + DEFAULTS['outside_mult'] * r['outside_total']

# theta anchor: the MEAN reach cost across House races that could be scored,
# replacing the old fixed "fully targetable" cost of 1.0.
_house_calc_reach = [r['reach'] for r in races if r['ch'] == 'H' and r['calc']]
anchor = sum(_house_calc_reach) / len(_house_calc_reach)

total_races = len(races) + len(excluded_races)   # every race on the board, scored or not

raw_by_race = {}
V_by_race = {}
for r in races:
    if r['calc']:
        c_eff = DEFAULTS['c_house'] * DEFAULTS['senate_mult'] if r['ch'] == 'S' else DEFAULTS['c_house']
        w = DEFAULTS['sen_val'] if r['ch'] == 'S' else 1.0
        V = c_eff * r['b'] + w * r['a']
        # P_dollars: the dollar cost of one full "impression pass" (touching
        # every voter in the race once), theta/reach-blended same as before,
        # just converted from the `reach` index into dollars via K.
        P_eff = DEFAULTS['theta'] * anchor + (1 - DEFAULTS['theta']) * r['reach']
        p_dollars = P_eff * K_DOLLARS_PER_REACH
        # passes: how many impression passes the campaign's money buys, out
        # of money_eff (its own money plus discounted outside money) rather
        # than the raw money field alone. No money floor needed any more: at
        # money==0, passes==0 and (prior_reach + passes)**-eta is still
        # finite (see CRRA note below).
        passes = r['money_eff'] / p_dollars
        # elasticity enters twice: once widening sigma (inside `a`, above),
        # once again here as an ease-of-persuasion multiplier on raw impact.
        #
        # Nrel: a dollar buys a FIXED FRACTION of reach (of P_dollars' full
        # pass), and that same fraction touches more real voters in a larger
        # electorate - so the value term scales up with electorate size,
        # not down. (Previously Nrel was entirely absent from raw, which
        # over-penalised large electorates - `a` alone carries a 1/N via
        # invN, with nothing to offset it.)
        #
        # (prior_reach + passes)**-eta / p_dollars: marginal utility of one
        # more dollar under CRRA utility u(prior_reach + D/P_dollars), i.e.
        # u'(.) * (1/P_dollars). This replaces the old D**-eta * P**(eta-1)
        # shape - which falls out of it exactly when passes >> prior_reach -
        # with a version that has no singularity at D == 0 (raw is then
        # simply V*el*Nrel*prior_reach**-eta/p_dollars, finite).
        raw = V * r['el'] * r['Nrel'] * (PRIOR_REACH + passes) ** -DEFAULTS['eta'] / p_dollars
        r['p_dollars'] = p_dollars
        r['passes'] = passes
    else:
        V, raw = None, 0.0   # calc==False races score 0 but still count in the denominator
        r['p_dollars'] = None
        r['passes'] = None
    V_by_race[r['race']] = V
    raw_by_race[r['race']] = raw

# mean (not max) raw score over EVERY race on the board: races with calc ==
# False contribute 0 to the sum, and excluded races contribute 0 too (they
# aren't in raw_by_race at all, but they are counted in total_races) - so the
# mean race, not the top race, scores impact == 100.
mean_raw = sum(raw_by_race.values()) / total_races

_outside_vals = [r['outside_total'] for r in races]
outside_totals = dict(races_with_outside=sum(1 for v in _outside_vals if v > 0),
                       sum=sum(_outside_vals))

meta = dict(forecast_date='2026-09-04', built=datetime.date.today().isoformat(),
            n=len(races), n_calc=sum(1 for r in races if r['calc']),
            sigma=SIG, k_dollars_per_reach=K_DOLLARS_PER_REACH,
            defaults=DEFAULTS,
            anchor=anchor, total_races=total_races, mean_raw=mean_raw, prior_reach=PRIOR_REACH,
            match_counts=match_counts, overrides=overridden_races,
            no_score=no_score_meta,
            outside_totals=outside_totals,
            excluded=dict(count=len(excluded_races), dem_only=len(dem_only_races),
                          rep_only=len(rep_only_races), races=excluded_races))
json.dump(dict(meta=meta, races=races), open(os.path.join(BASE, '..', '..', 'data.json'), 'w'),
          separators=(',', ':'))
print('wrote', len(races), 'races (', meta['n_calc'], 'calc )')
print('excluded', meta['excluded']['count'], 'races: dem_only=%d rep_only=%d' %
      (meta['excluded']['dem_only'], meta['excluded']['rep_only']), '->', excluded_races[:10])

# ---- preview with default params (impact = raw / mean_raw, mean race = 1.00) ----
scored = [r for r in races if r['calc']]
for r in scored:
    r['I'] = raw_by_race[r['race']] / mean_raw
print('%-7s %-18s %9s %7s %7s %9s  %s' % ('race', 'candidate', 'impact', 'cost', 'V', '$proj', 'rating'))
for r in sorted(scored, key=lambda x: -x['I'])[:20]:
    print('%-7s %-18s %9.1f %7.1f %7.2f %9.1fM  %s' %
          (r['race'] + ('*' if r['ch'] == 'S' else ''), r['name'][:18], r['I'], r['reach'],
           V_by_race[r['race']], r['proj'] / 1e6, r['rating']))
