# 2026 Marginal Impact Ranker

A static site that ranks competitive 2026 U.S. House and Senate races by
estimated marginal impact per donated dollar, using Silver Bulletin's public
forecast (win probabilities, vote-power index, elasticity) and FEC campaign
finance data. Everything runs client-side from a single JSON file — there is
no backend.

## The model

For each race, `a` = modeled probability a single vote flips that seat, and
`b` = Silver's vote-power index (probability a single vote there flips
control of its chamber). Then:

```
w        = sen_val if chamber == Senate else 1
c        = c_senate if chamber == Senate else c_house
V        = c*b + w*a
money    = max(receipts | coh | proj, 250_000)      # per the money-definition control
costEff  = theta*1 + (1-theta)*cost_index
raw      = V * money^(-eta) * costEff^(eta-1)
impact   = 100 * raw / max(raw over currently displayed races)
```

`eta` is a CRRA-style diminishing-returns exponent on money already raised;
`cost_index` is a static media-market ad-cost overspill index; `theta`
interpolates between "all spending is broadcast, fully subject to
market overspill" (0) and "all spending is precisely targetable" (1). The
top race shown is always exactly 100.0; everything else is relative to it.
All of this is recomputed live in the browser as the sliders move — see the
in-page "Methodology" section for the full explanation.

## Files

- `site/index.html` — the site. Self-contained (inline CSS/JS, no CDN, no
  build step). Fetches `./data.json` at load time.
- `site/data.json` — generated data, in the shape `{meta, races: [...]}`.
- `scripts/build.py` — one-shot generator that joins the source CSVs in
  `data/` into `site/data.json`.
- `scripts/refresh.py` — daily refresh: re-pulls live Silver Bulletin +
  FEC data and regenerates `site/data.json` (standard library only).
- `.github/workflows/refresh.yml` — runs `scripts/refresh.py` on a schedule.

## Deploying to GitHub Pages

1. Push this repo to GitHub.
2. Go to **Settings → Pages**.
3. Under **Build and deployment**, choose **Deploy from a branch**.
4. Pick your branch and the `/site` folder (or move `site/`'s contents to
   the repo root and choose `/root`, if you'd rather not have a `/site`
   path segment in the URL).
5. Save. GitHub Pages will serve `index.html` + `data.json` directly — no
   build step is needed since the page has no external dependencies.

## How the daily refresh works

`.github/workflows/refresh.yml` runs on a cron schedule (11:00 UTC daily)
and can also be triggered manually via `workflow_dispatch`. Each run:

1. Checks out the repo and sets up Python 3.
2. Runs `python scripts/refresh.py`, which:
   - Finds the newest published version of each of the four Silver Bulletin
     Datawrapper charts it depends on (House/Senate vote-power-index and
     House/Senate candidate charts) by probing upward from a known-good
     version until the next one 404s.
   - Rebuilds the race list from those charts, keeping the leading Democrat
     per race (or leading independent if there's no Democrat), and dropping
     R-vs-R and D-vs-D races and any race with a non-positive tipping-point
     value.
   - Pulls campaign-finance totals from the FEC's public API and matches
     each race's candidate by state+district and normalized last name,
     falling back to the highest-receipts candidate in that race (flagged
     `match: "top$"`) or to no match at all (`match: "none"`) when nothing
     lines up.
   - Reuses the previous run's money figures for any race where the FEC
     pull itself fails outright, so a transient FEC outage degrades
     gracefully instead of breaking the site. A failure to fetch the Silver
     Bulletin forecast data, by contrast, is treated as fatal — the script
     exits non-zero rather than writing incomplete data.
3. Commits and pushes `site/data.json` only if it actually changed.

### FEC API key

By default the refresh script uses the FEC's shared `DEMO_KEY`, which is
capped at 30 requests/hour and is easy to exhaust once the House and Senate
paginated pulls are both running. Get a free key at
<https://api.data.gov/signup/> and add it to the repo as an Actions secret
named `FEC_API_KEY` (**Settings → Secrets and variables → Actions → New
repository secret**). The workflow already passes it through as an
environment variable; no other changes are needed.

## Known limitations

- **Congressional-district geography** is based on 119th-Congress district
  lines. The 2025 mid-decade redistricting in TX, NC, OH, MO, CA, and UT
  means district boundaries (and therefore which voters/money a given race
  actually represents) are approximate for those states' affected seats.
- **ZIP-level population** feeding the media-market cost index is
  apportioned evenly within each county, not by actual ZIP population, so
  the cost index is a coarse approximation within multi-ZIP counties.
- **Ad cost** assumes a flat CPM across markets; the cost index reflects
  only the *media-market overspill* (how much of a broadcast dollar reaches
  voters outside the target district), not real differences in ad prices
  between markets.
