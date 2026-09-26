"""
RECESSION / INFLATION WATCHLIST
===============================
Long-term, low-maintenance watchlist built around James's thesis, with the
economic noise cut away:

  The only things that gain value are VICES and products that let the
  working class GET TO WORK and WORK LONGER HOURS.

  People don't riot when they realise they're trapped — they adapt and work
  more. That means smokes, booze, a punt, energy drinks, coffee, stimulants,
  fast food to work, fuel, and a cheap car kept on the road.

The scan is not a signal generator — it answers one question per ticker:
"has this thesis stock taken a nose dive, and is it sitting on (or heading
for) one of the blue lines?"

Blue line bands (read off James's MCD 12M / 6M charts):
  Big range size = 10^floor(log10(price))  ($236 → $100, $45 → $10, $4 → $1)
  Blue band      = 20%–30% of each big range  (MCD: $20–30, $120–130, $220–230)

"Three ranges" idea: price rarely holds after running 3 big ranges without
coming back to the pattern. `run_ranges` = (all-time high − lowest low in
the RUN_LOOKBACK_MONTHS before it) / big range size. 2.5+ is flagged as
extended.

Data: yfinance monthly bars, full history (not the MySQL prices table, which
only holds ~5 years and only US tickers) — so ATHs and blue-line touches
match what TradingView shows on the 12M/6M charts.

Usage:
    python db_recession_watchlist.py
"""

import os
import json
import math
from datetime import datetime

BASE_DIR     = os.path.dirname(os.path.abspath(__file__))
RESULTS_FILE = os.path.join(BASE_DIR, 'last_recession_results.json')

BLUE_LOW_PCT        = 0.20   # blue band bottom, as a fraction of the big range
BLUE_HIGH_PCT       = 0.30   # blue band top
AT_BLUE_BUFFER_PCT  = 2.0    # within this % above the band top still counts as "at" it
NOSE_DIVE_PCT       = -15.0  # drawdown from ATH needed to call it a nose dive
APPROACH_PCT        = 10.0   # next blue band below is within this % → "approaching"
EXTENDED_RANGES     = 2.5    # run of this many big ranges = extended
RUN_LOOKBACK_MONTHS = 60     # window before the ATH used to find the run's starting low
MIN_MONTHS          = 24


# ── Thesis themes ─────────────────────────────────────────────────────────────
# Every theme belongs to one pillar:
#   'vice' — what people keep buying when they're trapped
#   'work' — what gets them to work and keeps them there longer
#   'side' — outside the core thesis (benchmark / macro side-bets); shown on the
#            page but never in the shortlist or the TradingView list
# Each theme: key, pillar, title, rationale, tickers {symbol: note}.
# '.AX' symbols are ASX (TradingView prefix ASX:). 'added' marks themes that
# weren't named in the original conversation but fit the pillar.

PILLARS = [
    ('vice', 'Vices'),
    ('work', 'Get to Work & Work Longer'),
    ('side', 'Outside the Core Thesis'),
]

THEMES = [
    # ── Vices ────────────────────────────────────────────────────────────────
    {
        'key': 'smokes', 'pillar': 'vice', 'title': 'Smokes',
        'rationale': "Cheap, habitual, and people cut food before they cut smokes.",
        'tickers': {
            'MO':  'Altria — Marlboro (US)',
            'PM':  'Philip Morris Intl — Marlboro ex-US, Zyn, IQOS',
            'BTI': 'British American Tobacco — Lucky Strike, Vuse, Velo',
            'TPB': 'Turning Point Brands — Zig-Zag, Stoker\'s, nicotine pouches',
        },
    },
    {
        'key': 'booze', 'pillar': 'vice', 'title': 'Booze', 'added': True,
        'rationale': "The other end of the long shift — cheap beer and spirits hold up "
                     "when everything else gets cut.",
        'tickers': {
            'STZ':  'Constellation — Corona, Modelo',
            'TAP':  'Molson Coors — cheap beer',
            'DEO':  'Diageo — Smirnoff, Johnnie Walker, Guinness',
            'BF-B': 'Brown-Forman — Jack Daniel\'s',
            'SAM':  'Boston Beer — Twisted Tea, Truly',
        },
    },
    {
        'key': 'gambling', 'pillar': 'vice', 'title': 'Gambling', 'added': True,
        'rationale': "Trapped people buy hope — lotto tickets and sports bets are the "
                     "cheapest way out on paper.",
        'tickers': {
            'DKNG': 'DraftKings — sports betting',
            'FLUT': 'Flutter — FanDuel, Sportsbet',
            'CZR':  'Caesars Entertainment',
            'LNW':  'Light & Wonder — pokies',
        },
    },
    {
        'key': 'asx_vice', 'pillar': 'vice', 'title': 'ASX Vices', 'added': True,
        'rationale': "Same vices on the ASX — bottle-o, lotto, pokies, fast food.",
        'tickers': {
            'EDV.AX': 'Endeavour — Dan Murphy\'s, BWS, pubs & pokies',
            'TLC.AX': 'The Lottery Corporation',
            'ALL.AX': 'Aristocrat — pokies',
            'CKF.AX': 'Collins Foods — KFC Australia',
            'DMP.AX': 'Domino\'s Pizza Enterprises',
        },
    },

    # ── Get to work & work longer ────────────────────────────────────────────
    {
        'key': 'energy', 'pillar': 'work', 'title': 'Energy Drinks & Coffee',
        'rationale': "You need energy to work more. Energy drinks and coffee are the "
                     "cheapest way to buy another few hours.",
        'tickers': {
            'MNST': 'Monster Beverage',
            'CELH': 'Celsius',
            'KDP':  'Keurig Dr Pepper — K-Cups, Ghost energy',
            'SBUX': 'Starbucks',
            'BROS': 'Dutch Bros',
        },
    },
    {
        'key': 'pharma', 'pillar': 'work', 'title': 'Stimulant Pharma',
        'rationale': "Vyvanse / speed — the prescription version of an energy drink. "
                     "Generics win as people trade down.",
        'tickers': {
            'TAK':  'Takeda — Vyvanse originator',
            'TEVA': 'Teva — largest generics maker, ADHD generics',
            'VTRS': 'Viatris — generics',
            'AMRX': 'Amneal — generics incl. stimulants',
        },
    },
    {
        'key': 'fastfood', 'pillar': 'work', 'title': 'Fast Food',
        'rationale': "No time to cook when you're working longer hours — easier to order "
                     "food to work. MCD is the template: it likes the blue lines and "
                     "hasn't got there yet.",
        'tickers': {
            'MCD':  'McDonald\'s — the template chart',
            'YUM':  'Yum! — KFC, Taco Bell, Pizza Hut',
            'QSR':  'Restaurant Brands — Burger King, Tim Hortons, Popeyes',
            'DPZ':  'Domino\'s',
            'WEN':  'Wendy\'s',
            'PZZA': 'Papa John\'s',
            'JACK': 'Jack in the Box',
            'WING': 'Wingstop',
        },
    },
    {
        'key': 'convenience', 'pillar': 'work', 'title': 'Delivery, Rides & Servo',
        'rationale': "Food to the job site, a ride to work, and the servo where the "
                     "fuel, smokes and energy drinks get bought on the way.",
        'tickers': {
            'DASH': 'DoorDash — food to work',
            'UBER': 'Uber — rides to work, Uber Eats',
            'CASY': 'Casey\'s — servo + pizza',
            'MUSA': 'Murphy USA — cheap fuel, tobacco, energy drinks',
        },
    },
    {
        'key': 'cars', 'pillar': 'work', 'title': 'Cheap Cars & Keeping Them Running',
        'rationale': "Low-cost, easy-to-fix cars — people keep the old car on the road "
                     "to get to work instead of buying new.",
        'tickers': {
            'AZO':  'AutoZone — parts',
            'ORLY': 'O\'Reilly Automotive — parts',
            'GPC':  'Genuine Parts (NAPA)',
            'LKQ':  'LKQ — recycled / aftermarket parts',
            'CPRT': 'Copart — salvage auctions',
            'KMX':  'CarMax — used cars',
            'TM':   'Toyota — cheap, reliable, easy to fix',
        },
    },
    {
        'key': 'fuel', 'pillar': 'work', 'title': 'Petrol',
        'rationale': "Everything that moves needs fuel, and so does the drive to work — "
                     "it's not just mortgages that stop at 7% rates.",
        'tickers': {
            'XOM': 'Exxon Mobil',
            'CVX': 'Chevron',
            'COP': 'ConocoPhillips',
            'VLO': 'Valero — refiner',
            'MPC': 'Marathon Petroleum — refiner',
            'PSX': 'Phillips 66 — refiner',
        },
    },
    {
        'key': 'workgear', 'pillar': 'work', 'title': 'Work Gear & Tools', 'added': True,
        'rationale': "Boots, workwear and hired tools — what the working class needs "
                     "to turn up and do the extra hours.",
        'tickers': {
            'BOOT': 'Boot Barn — work boots & workwear',
            'WWW':  'Wolverine — Cat / Wolverine work boots',
            'URI':  'United Rentals — tool & equipment hire',
        },
    },
    {
        'key': 'asx_work', 'pillar': 'work', 'title': 'ASX Get to Work', 'added': True,
        'rationale': "Servo fuel and car parts on the ASX.",
        'tickers': {
            'ALD.AX': 'Ampol — fuel',
            'VEA.AX': 'Viva Energy — Shell / Coles Express, OTR',
            'BAP.AX': 'Bapcor — Autobarn, Burson car parts',
        },
    },

    # ── Outside the core thesis ──────────────────────────────────────────────
    {
        'key': 'canary', 'pillar': 'side', 'title': 'Tech Canary',
        'rationale': "QQQ is the surveillance piggy bank — it outperforms no matter what, "
                     "until it doesn't. OpenAI and Anthropic holding off on IPOs and the free "
                     "government money drying up are the cracks to watch. Benchmark, not a buy.",
        'tickers': {'QQQ': 'Nasdaq 100 — the benchmark'},
    },
    {
        'key': 'space', 'pillar': 'side', 'title': 'Space',
        'rationale': "Tech might not have another card to play after AI — the only thing "
                     "next is space. Macro side-bet, not the working-class thesis.",
        'tickers': {
            'RKLB': 'Rocket Lab',
            'ASTS': 'AST SpaceMobile',
            'LUNR': 'Intuitive Machines',
            'LMT':  'Lockheed Martin',
        },
    },
    {
        'key': 'food', 'pillar': 'side', 'title': 'Food & Rent',
        'rationale': "People eat and need a roof no matter what — but staples and "
                     "landlords are necessities, not vices or work enablers.",
        'tickers': {
            'CAG':  'Conagra — frozen / cheap meals',
            'TSN':  'Tyson Foods',
            'ADM':  'Archer-Daniels-Midland — grain',
            'INVH': 'Invitation Homes — single-family rentals',
            'UPBD': 'Upbound — Rent-A-Center, rent-to-own',
        },
    },
]


def all_tickers(pillars=None):
    """Every watchlist symbol in theme order, de-duplicated, optionally by pillar."""
    seen = []
    for theme in THEMES:
        if pillars and theme['pillar'] not in pillars:
            continue
        for t in theme['tickers']:
            if t not in seen:
                seen.append(t)
    return seen


def core_tickers():
    """Vices + get-to-work — the tickers the thesis actually buys."""
    return all_tickers(pillars=('vice', 'work'))


def tradingview_symbol(ticker):
    if ticker.endswith('.AX'):
        return f"ASX:{ticker[:-3]}"
    return ticker.replace('-', '.')   # BF-B (Yahoo) → BF.B (TradingView)


def tradingview_list():
    return ','.join(tradingview_symbol(t) for t in core_tickers())


# ── Blue line maths ───────────────────────────────────────────────────────────

def big_range_size(price):
    """$100 for a $236 stock, $10 for $45, $1 for $4."""
    if price is None or price <= 0:
        return None
    return 10.0 ** math.floor(math.log10(price))


def blue_band(range_low, size):
    return range_low + size * BLUE_LOW_PCT, range_low + size * BLUE_HIGH_PCT


def blue_bands_near(price, size):
    """The blue band in the price's own big range and the one below it."""
    base = math.floor(price / size) * size
    bands = [blue_band(base, size)]
    if base - size >= 0:
        bands.append(blue_band(base - size, size))
    return bands


def analyse(ticker, df):
    """
    df: monthly bars (open/high/low/close), oldest first.
    Returns a result dict, or None if there isn't enough history.
    """
    if df is None or len(df) < MIN_MONTHS:
        return None

    price = float(df['close'].iloc[-1])
    size  = big_range_size(price)
    if not size:
        return None

    ath_idx  = df['high'].idxmax()
    ath      = float(df['high'].max())
    drawdown = (price / ath - 1) * 100

    # Run into the ATH, in big ranges ("never 3")
    ath_pos    = df.index.get_loc(ath_idx)
    run_window = df.iloc[max(0, ath_pos - RUN_LOOKBACK_MONTHS):ath_pos + 1]
    run_low    = float(run_window['low'].min())
    run_ranges = (ath - run_low) / size

    # Current blue band / next one below
    at_band = None
    below   = None
    for lo, hi in blue_bands_near(price, size):
        if lo <= price <= hi * (1 + AT_BLUE_BUFFER_PCT / 100):
            at_band = (lo, hi)
        elif hi < price and below is None:
            below = (lo, hi)
    target   = at_band or below
    distance = (price / target[1] - 1) * 100 if target else None

    # Has this stock respected blue lines before? A "hold" = a month whose low
    # tagged a blue band and closed back above the band bottom.
    holds = 0
    for lo_p, cl_p in zip(df['low'].astype(float), df['close'].astype(float)):
        band_lo, band_hi = blue_band(math.floor(lo_p / size) * size, size)
        if band_lo <= lo_p <= band_hi and cl_p >= band_lo:
            holds += 1

    dove = drawdown <= NOSE_DIVE_PCT
    if at_band and dove:
        status = 'AT BLUE'
    elif at_band:
        status = 'ON BLUE'
    elif dove and distance is not None and distance <= APPROACH_PCT:
        status = 'APPROACHING'
    elif dove:
        status = 'DIVING'
    else:
        status = 'WATCH'

    return {
        'ticker':      ticker,
        'price':       round(price, 4),
        'ath':         round(ath, 4),
        'ath_date':    ath_idx.strftime('%Y-%m'),
        'drawdown':    round(drawdown, 1),
        'range_size':  size,
        'blue_low':    round(target[0], 2) if target else None,
        'blue_high':   round(target[1], 2) if target else None,
        'blue_dist':   round(distance, 1) if distance is not None else None,
        'run_ranges':  round(run_ranges, 2),
        'extended':    run_ranges >= EXTENDED_RANGES,
        'blue_holds':  holds,
        'status':      status,
        'first_month': df.index[0].strftime('%Y-%m'),
        'date':        df.index[-1].strftime('%Y-%m-%d'),
    }


# ── Data ──────────────────────────────────────────────────────────────────────

def get_monthly(ticker):
    import yfinance as yf
    df = yf.Ticker(ticker).history(period='max', interval='1mo', auto_adjust=False)
    if df is None or df.empty:
        return None
    df = df.rename(columns=str.lower)[['open', 'high', 'low', 'close']].dropna()
    df = df[(df > 0).all(axis=1)]
    if df.index.tz is not None:
        df.index = df.index.tz_localize(None)
    return df


STATUS_ORDER = {'AT BLUE': 0, 'APPROACHING': 1, 'ON BLUE': 2, 'DIVING': 3, 'WATCH': 4}


def run_recession_scan(log_callback=None):
    def log(msg):
        print(msg)
        if log_callback:
            log_callback(msg + '\n')

    tickers = all_tickers()
    core    = set(core_tickers())
    log('=' * 60)
    log('RECESSION / INFLATION WATCHLIST')
    log('=' * 60)
    log(f"Started: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    log(f"Checking {len(tickers)} tickers ({len(core)} core vice / work) against the "
        f"blue lines (monthly, full history)\n")

    results, failed = [], []
    for i, ticker in enumerate(tickers, 1):
        try:
            r = analyse(ticker, get_monthly(ticker))
            if r:
                r['core'] = ticker in core
                results.append(r)
                log(f"[{i}/{len(tickers)}] {ticker:7} {r['status']:11} ${r['price']:,.2f}  "
                    f"{r['drawdown']:+.1f}% from ATH  blue {r['blue_low']}–{r['blue_high']}")
            else:
                failed.append(ticker)
                log(f"[{i}/{len(tickers)}] {ticker}: not enough history")
        except Exception as e:
            failed.append(ticker)
            log(f"[{i}/{len(tickers)}] {ticker}: ERROR — {str(e)[:60]}")

    results.sort(key=lambda r: (STATUS_ORDER[r['status']],
                                r['blue_dist'] if r['blue_dist'] is not None else 999))

    output = {
        'scan_date':       datetime.now().strftime('%Y-%m-%d %H:%M'),
        'total':           sum(1 for r in results
                               if r['core'] and r['status'] in ('AT BLUE', 'APPROACHING')),
        'tickers_scanned': len(tickers),
        'failed':          failed,
        'results':         results,
    }
    with open(RESULTS_FILE, 'w') as f:
        json.dump(output, f)

    log(f"\n{'='*60}")
    log(f"COMPLETE — {output['total']} core vice / work stocks at or approaching a blue line, "
        f"{len(failed)} failed")
    log('=' * 60)
    return output


def load_last_recession_results():
    if os.path.exists(RESULTS_FILE):
        with open(RESULTS_FILE) as f:
            return json.load(f)
    return None


if __name__ == '__main__':
    run_recession_scan()
