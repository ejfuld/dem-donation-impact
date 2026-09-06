"""Join Silver Bulletin forecast + media-market cost index + FEC money -> data.json"""
import csv, json, math, datetime, os, statistics as _st
BASE = os.path.join(os.path.dirname(__file__), '..', 'data')
SIG = {'H': 6.65, 'S': 6.69}
ELECTION = datetime.date(2026, 11, 3)
CYCLE_START = datetime.date(2025, 1, 1)
MONEY_FLOOR = 1_000_000.0


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
        receipts = float(m.get('receipts') or 0) or MONEY_FLOOR
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
        if tip <= 0:
            a = None
            N = None
            calc = False
        else:
            z = phi_inv(p)
            sig = SIG[ch] * el
            invN = vpi / tip
            a = invN * phi(z) / sig
            N = 1.0 / invN
            calc = True

        races.append(dict(
            race=code, ch=ch, name=r['dem_last'], party=marg.get(code, {}).get('party', 'D'),
            rating=r['rating'] or ('Toss-up' if 0.4 < p < 0.6 else ''),
            tip=tip, vpi=vpi, el=el, p=p,
            margin=float(marg.get(code, {}).get('margin') or 0),
            a=a,                             # oc P(one vote flips the seat)
            b=vpi,                           # oc P(one vote flips the chamber)
            cost=cost.get(code, 8.0),        # media-market overspill factor (per constituent)
            N=N,                             # oc size of the electorate
            receipts=receipts, coh=coh,
            proj=coh + rate * months_left,   # cash on hand + extrapolated contributions
            rate=rate, cov=cov,
            match=m.get('match', 'none'),
            calc=calc,
            Nrel=None, reach=None))          # filled in below once the House median N is known

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

excluded_races = sorted(dem_only_races + rep_only_races)
meta = dict(forecast_date='2026-09-04', built=datetime.date.today().isoformat(),
            n=len(races), n_calc=sum(1 for r in races if r['calc']),
            sigma=SIG, money_floor=MONEY_FLOOR,
            defaults=dict(c_house=25.0, senate_mult=0.75, sen_val=13.05, eta=0.72,
                          theta=0.40, money='proj'),
            excluded=dict(count=len(excluded_races), dem_only=len(dem_only_races),
                          rep_only=len(rep_only_races), races=excluded_races))
json.dump(dict(meta=meta, races=races), open(os.path.join(BASE, '..', 'site', 'data.json'), 'w'),
          separators=(',', ':'))
print('wrote', len(races), 'races (', meta['n_calc'], 'calc )')
print('excluded', meta['excluded']['count'], 'races: dem_only=%d rep_only=%d' %
      (meta['excluded']['dem_only'], meta['excluded']['rep_only']), '->', excluded_races[:10])

# ---- preview with default params ----
D = meta['defaults']
scored = [r for r in races if r['calc']]
for r in scored:
    c_eff = D['c_house'] * D['senate_mult'] if r['ch'] == 'S' else D['c_house']
    w = D['sen_val'] if r['ch'] == 'S' else 1.0
    V = c_eff * r['b'] + w * r['a']
    r['V'] = V
    money_used = max(r['proj'], MONEY_FLOOR)
    P_eff = D['theta'] * 1.0 + (1 - D['theta']) * r['reach']
    r['I'] = V * (money_used ** -D['eta']) * (P_eff ** (D['eta'] - 1))
mx = max(r['I'] for r in scored)
for r in scored:
    r['I'] = 100 * r['I'] / mx
print('%-7s %-18s %5s %7s %7s %9s  %s' % ('race', 'candidate', 'impact', 'cost', 'V', '$proj', 'rating'))
for r in sorted(scored, key=lambda x: -x['I'])[:20]:
    print('%-7s %-18s %5.1f %7.1f %7.2f %9.1fM  %s' %
          (r['race'] + ('*' if r['ch'] == 'S' else ''), r['name'][:18], r['I'], r['reach'],
           r['V'], r['proj'] / 1e6, r['rating']))
