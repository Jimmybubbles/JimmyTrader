"""
REFRESH TICKER UNIVERSE (CSV/5000.csv)
======================================
1. Downloads daily prices for every ticker in CSV/5000.csv
2. Removes tickers that are delisted — same rule as website/db_daily_update.py:
   Yahoo answers "no data" for it, or its last bar is more than DELIST_DAYS old.
   Batch downloads only collect data; anything a batch misses is checked on its
   own (verify()). A ticker Yahoo only RATE-LIMITED is never treated as
   delisted — it's retried with a back-off, and kept if it still can't be checked.
3. Screens Yahoo Finance for the largest companies (by market cap) listed on
   the main exchange of each overseas market in MARKETS and appends them
4. Caches all price data to data_cache/daily_<period>.pkl for the backtests

Progress is saved after every batch (data_cache/refresh_progress_<period>.pkl)
so a crash or rate-limit stall resumes where it left off. Removed tickers are
written to CSV/removed_tickers.txt with the reason. If more than MAX_REMOVE_PCT
of the list would be removed, nothing is written — that means Yahoo was
misbehaving, not that half the market delisted.

Overseas picks must be ordinary shares with a sector, BASED IN that market's country
(see DOMICILE_OK for the usual exceptions) — Yahoo's
region screen includes foreign lines like NVIDIA's NVD.DE or SAP's 1SAP.MI — and not already
in the list under another spelling — each market is topped up to TOP_N.

Usage:
    python refresh_universe.py                    # 3y of data, top 25 per market
    python refresh_universe.py 5y 40
    python refresh_universe.py --overseas-only    # redo just step 3, reusing the price cache
"""

import os
import sys
import re
import time
import unicodedata
import pickle
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor

import pandas as pd
import yfinance as yf

from yfinance import EquityQuery as Q
from yfinance.exceptions import YFRateLimitError

HERE           = os.path.dirname(os.path.abspath(__file__))
TICKER_FILE    = os.path.join(HERE, 'CSV', '5000.csv')
REMOVED_LOG    = os.path.join(HERE, 'CSV', 'removed_tickers.txt')
CACHE_DIR      = os.path.join(HERE, 'data_cache')
OVERSEAS_ONLY  = '--overseas-only' in sys.argv
_POS           = [a for a in sys.argv[1:] if not a.startswith('--')]
PERIOD         = _POS[0] if len(_POS) > 0 else '3y'
TOP_N          = int(_POS[1]) if len(_POS) > 1 else 25
PROGRESS_FILE  = os.path.join(CACHE_DIR, f'refresh_progress_{PERIOD}.pkl')
DELIST_DAYS    = 30
CHUNK          = 100
PAUSE          = 3                       # seconds between batches
BACKOFF        = (60, 120, 240, 300, 300, 300)
MAX_REMOVE_PCT = 20
CANARY         = 'SPY'

# Yahoo region code → (country, suffix of that market's main exchange).
# Australia is left out — ASX tickers are already in the list / the ASX section.
MARKETS = {
    'gb': ('United Kingdom', '.L'),   'de': ('Germany', '.DE'),    'fr': ('France', '.PA'),
    'nl': ('Netherlands', '.AS'),     'ch': ('Switzerland', '.SW'), 'es': ('Spain', '.MC'),
    'it': ('Italy', '.MI'),           'se': ('Sweden', '.ST'),     'dk': ('Denmark', '.CO'),
    'jp': ('Japan', '.T'),            'hk': ('Hong Kong', '.HK'),  'in': ('India', '.NS'),
    'kr': ('South Korea', '.KS'),     'tw': ('Taiwan', '.TW'),     'sg': ('Singapore', '.SI'),
    'ca': ('Canada', '.TO'),          'br': ('Brazil', '.SA'),
}


def log(msg):
    print(msg, flush=True)


def _download_once(tickers):
    """One batch yf.download call → (data, missing).

    Batch downloads are only trusted for what they DO return. Under partial
    rate limiting Yahoo silently returns empty frames (no error recorded) for
    live tickers like MSFT, so anything missing just goes on to verify().
    CANARY (SPY) rides along: if even SPY is empty, the whole batch was
    rate-limited → (None, None) so the caller backs off.
    """
    raw = yf.download(list(dict.fromkeys(tickers + [CANARY])), period=PERIOD, interval='1d',
                      auto_adjust=False, group_by='ticker', progress=False, threads=4)
    try:
        if not len(raw[CANARY].dropna(subset=['Close'])):
            return None, None
    except (KeyError, TypeError):
        return None, None
    data, missing = {}, []
    for t in tickers:
        try:
            df = raw[t][['Open', 'High', 'Low', 'Close', 'Volume']].dropna(subset=['Close'])
        except (KeyError, TypeError):
            df = None
        if df is not None and len(df):
            df.columns = ['open', 'high', 'low', 'close', 'volume']
            data[t] = df
        else:
            missing.append(t)
    return data, missing


def save(progress):
    with open(PROGRESS_FILE, 'wb') as f:
        pickle.dump(progress, f)


def fetch(tickers, progress, label):
    """Batch-download `tickers`, backing off on rate limits. Updates `progress` in place."""
    todo = [t for t in tickers if t not in progress['done']]
    log(f"{label}: {len(tickers) - len(todo)} already done, {len(todo)} to download")
    for i in range(0, len(todo), CHUNK):
        batch = todo[i:i + CHUNK]
        data, missing = {}, batch
        for wait in BACKOFF:
            got, miss = _download_once(batch)
            if got is not None:
                data, missing = got, miss
                break
            log(f"  batch rate-limited — waiting {wait}s")
            time.sleep(wait)
        progress['data'].update(data)
        progress['missing'].update(missing)
        progress['done'].update(batch)
        log(f"  {label}: {min(i + CHUNK, len(todo))}/{len(todo)}  "
            f"(ok {len(progress['data'])}, to verify {len(progress['missing'])})")
        save(progress)
        time.sleep(PAUSE)


def _canary_ok():
    """True if Yahoo is reachable and answering right now (SPY loads)."""
    try:
        return len(yf.Ticker(CANARY).history(period='5d')) > 0
    except Exception:
        return False


def verify(progress, label):
    """Check each ticker a batch didn't return ON ITS OWN. A single-ticker
    history() call raises YFRateLimitError when throttled (unlike the batch).
    It does NOT raise on a network drop though — it just returns empty — so an
    empty answer only counts as "no data" if SPY still loads straight after."""
    todo = sorted(progress['missing'])
    log(f"{label}: verifying {len(todo)} tickers one at a time")
    for n, t in enumerate(todo, 1):
        result = None
        for wait in BACKOFF + (None,):
            try:
                result = yf.Ticker(t).history(period=PERIOD, auto_adjust=False)
            except YFRateLimitError:
                result = None
            except Exception as e:
                result = str(e) or type(e).__name__
            if result is not None and not isinstance(result, str) and len(result):
                break
            if result is not None and _canary_ok():
                break                      # Yahoo is fine → the empty answer is real
            result = None
            if wait is None:
                break
            log(f"  {t}: Yahoo unreachable / rate-limited — waiting {wait}s")
            time.sleep(wait)
        if result is None:
            progress['unchecked'].add(t)
        elif isinstance(result, str) or not len(result):
            progress['no_data'][t] = result if isinstance(result, str) else 'no price data'
        else:
            df = result[['Open', 'High', 'Low', 'Close', 'Volume']].dropna(subset=['Close'])
            df.columns = ['open', 'high', 'low', 'close', 'volume']
            df.index = df.index.tz_localize(None).normalize()
            progress['data'][t] = df
        progress['missing'].discard(t)
        if n % 25 == 0 or n == len(todo):
            log(f"  {label}: verified {n}/{len(todo)}  (no data {len(progress['no_data'])}, "
                f"unchecked {len(progress['unchecked'])})")
            save(progress)
        time.sleep(0.5)


def screen_market(region, suffix, keep):
    """Listings on the market's main exchange that pass the cheap `keep` filter,
    biggest first. Yahoo ranks every line by the WHOLE company's market cap, so on
    Xetra / Milan / São Paulo the first few hundred are foreign giants' secondary
    lines — keep paging (250 at a time) until there are enough real candidates."""
    found = []
    for offset in range(0, 2000, 250):
        for wait in BACKOFF + (None,):
            try:
                quotes = yf.screen(Q('eq', ['region', region]), sortField='intradaymarketcap',
                                   sortAsc=False, size=250, offset=offset)['quotes']
                break
            except YFRateLimitError:
                if wait is None:
                    raise
                log(f"  screener rate-limited — waiting {wait}s")
                time.sleep(wait)
        found += [x for x in quotes if x['symbol'].endswith(suffix) and keep(x)]
        if len(found) >= TOP_N * 3 or len(quotes) < 250:
            break
        time.sleep(1)
    return found


# Rough USD value of one unit of each quote currency — only used for the
# MIN_TURNOVER_USD liquidity cut-off, so approximate rates are fine.
USD_PER = {'USD': 1, 'GBp': 0.0135, 'GBP': 1.35, 'EUR': 1.17, 'CHF': 1.25, 'SEK': 0.106,
           'DKK': 0.157, 'JPY': 0.0068, 'HKD': 0.128, 'INR': 0.0115, 'KRW': 0.00072,
           'TWD': 0.033, 'SGD': 0.78, 'CAD': 0.72, 'BRL': 0.19}
# Average daily $ traded a pick needs — weeds out preference shares (BP-A.L, BCE-PL.TO),
# depositary receipts (UGBD.SI) and dead funds that otherwise look like big companies
MIN_TURNOVER_USD = 1_000_000


def profile(symbol):
    """(quoteType, sector, country, avg daily $ turnover) from Yahoo's profile. An empty
    profile is how a throttled .info call often looks, so it's retried like a rate
    limit — a big company must never lose its spot just because Yahoo was busy."""
    for wait in (20, 60, 120, None):
        try:
            info = yf.Ticker(symbol).info or {}
            if info.get('quoteType'):
                vol = info.get('averageDailyVolume3Month') or info.get('averageVolume') or 0
                px = info.get('regularMarketPrice') or info.get('previousClose') or 0
                turnover = vol * px * USD_PER.get(info.get('currency'), 0)
                return info.get('quoteType'), info.get('sector'), info.get('country'), turnover
        except Exception:
            pass
        if wait is None:
            break
        time.sleep(wait)
    return None, None, None, 0


# Companies are only picked on the market of the country they're based in, so a
# foreign company's secondary line (NVD.DE, 1SAP.MI) never stands in for the real
# thing. These are the usual, legitimate exceptions per market.
DOMICILE_OK = {
    'hk': {'China', 'Macau', 'Bermuda', 'Cayman Islands'},
    'gb': {'Jersey', 'Guernsey', 'Isle of Man', 'Ireland', 'Switzerland'},
    'fr': {'Netherlands', 'Luxembourg'},            # Airbus, Stellantis, ArcelorMittal
    'it': {'Netherlands', 'Luxembourg'},            # Ferrari, Stellantis, Exor, Tenaris
    'nl': {'Luxembourg', 'Belgium'},
    'sg': {'Bermuda', 'China'},
}
# Secondary-line ticker patterns: Milan's "1XXX.MI" foreign segment, Brazilian BDRs
CROSS_LISTING = re.compile(r'^1[A-Z0-9]+\.MI$|3[1-59]\.SA$')


_NAME_NOISE = re.compile(r'\b(INC|CORP|CORPORATION|CO|COMPANY|LTD|LIMITED|PLC|SA|AG|SE|NV|AB|ASA|SPA|'
                         r'HOLDINGS?|GROUP|THE|CLASS [A-Z])\b')


def norm_name(name):
    """'Apple Inc.' and 'APPLE INC' → 'APPLE', so the same company matches across listings."""
    ascii_name = unicodedata.normalize('NFKD', str(name)).encode('ascii', 'ignore').decode()  # Itaú → Itau
    return ' '.join(_NAME_NOISE.sub(' ', re.sub(r'[^A-Z0-9 ]', ' ', ascii_name.upper())).split())


def pick_overseas(have, seen_names):
    """Top TOP_N real, non-US, not-already-listed companies per market → new CSV rows."""
    new_rows = []
    for region, (country, suffix) in MARKETS.items():
        try:
            candidates = screen_market(region, suffix, lambda x: (
                x['symbol'] not in have and not CROSS_LISTING.search(x['symbol'])
                and norm_name(x.get('longName') or x.get('shortName') or '') not in seen_names))
        except Exception as e:
            log(f"  {country}: screen failed — {e}")
            continue
        home = {country} | DOMICILE_OK.get(region, set())
        picked, skipped = [], []
        for i in range(0, len(candidates), 8):
            chunk = candidates[i:i + 8]
            with ThreadPoolExecutor(4) as ex:
                profiles = list(ex.map(profile, [x['symbol'] for x in chunk]))
            for x, (qtype, sector, dom, turnover) in zip(chunk, profiles):
                name = (x.get('longName') or x.get('shortName') or x['symbol']).strip()
                why = ('no profile' if not qtype else 'not a share' if qtype != 'EQUITY'
                       else 'no sector' if not sector else f'based in {dom}' if dom not in home
                       else f'illiquid ${turnover / 1e6:.2f}M/day' if turnover < MIN_TURNOVER_USD
                       else 'already listed' if norm_name(name) in seen_names else None)
                if why:
                    skipped.append(f"{x['symbol']} ({why})")
                    continue
                have.add(x['symbol'])
                seen_names.add(norm_name(name))
                picked.append({'Ticker': x['symbol'], 'Company': name, 'Sector': sector, 'Country': country})
                if len(picked) == TOP_N:
                    break
            if len(picked) == TOP_N:
                break
        new_rows += picked
        log(f"  {country}: +{len(picked)}" + (f"  (skipped {len(skipped)}: {', '.join(skipped[:6])}"
                                               f"{' …' if len(skipped) > 6 else ''})" if skipped else ''))
    return new_rows


def main():
    if OVERSEAS_ONLY:
        return redo_overseas()

    today = pd.Timestamp(datetime.now().date())
    os.makedirs(CACHE_DIR, exist_ok=True)
    progress = {'data': {}, 'missing': set(), 'no_data': {}, 'done': set(), 'unchecked': set()}
    if os.path.exists(PROGRESS_FILE):
        with open(PROGRESS_FILE, 'rb') as f:
            progress.update(pickle.load(f))
        progress['missing'] |= progress['unchecked']   # give rate-limited ones another go
        progress['unchecked'] = set()
        log(f"Resuming from {PROGRESS_FILE}")

    csv = pd.read_csv(TICKER_FILE)
    tickers = list(dict.fromkeys(csv['Ticker'].astype(str)))
    log(f"5000.csv: {len(tickers)} tickers")

    # ── 1-2. Download existing list, find the dead ones ───────────────────────
    fetch(tickers, progress, 'existing')
    verify(progress, 'existing')

    removed = {t: f"no data on yfinance ({progress['no_data'][t][:60]})"
               for t in tickers if t in progress['no_data']}
    for t in tickers:
        df = progress['data'].get(t)
        if df is not None and (today - df.index[-1]).days > DELIST_DAYS:
            removed[t] = f"no data since {df.index[-1].date()}"

    pct = len(removed) / len(tickers) * 100
    log(f"{len(removed)} delisted ({pct:.1f}%), {len(progress['unchecked'])} unchecked (kept)")
    if pct > MAX_REMOVE_PCT:
        log(f"ABORT: over {MAX_REMOVE_PCT}% flagged — Yahoo is probably rate-limiting. "
            f"Nothing written; rerun later to resume.")
        return

    # ── 3. Overseas: top companies by market cap per market ──────────────────
    have = set(tickers) - set(removed)
    seen_names = set(csv.loc[csv['Ticker'].isin(have), 'Company'].map(norm_name))
    new_rows = pick_overseas(have, seen_names)

    if new_rows:
        fetch([r['Ticker'] for r in new_rows], progress, 'overseas')
        verify(progress, 'overseas')
        new_rows = [r for r in new_rows if r['Ticker'] in progress['data']
                    and (today - progress['data'][r['Ticker']].index[-1]).days <= DELIST_DAYS]

    # ── Write CSV, removal log, price cache ──────────────────────────────────
    csv = csv[~csv['Ticker'].isin(removed)].drop_duplicates('Ticker')
    if new_rows:
        csv = pd.concat([csv, pd.DataFrame(new_rows)[['Ticker', 'Company', 'Sector']]], ignore_index=True)
    csv.to_csv(TICKER_FILE, index=False)

    with open(REMOVED_LOG, 'a', encoding='utf-8') as f:
        f.write(f"# refresh_universe.py {datetime.now():%Y-%m-%d %H:%M} — {len(removed)} removed\n")
        for t, why in sorted(removed.items()):
            f.write(f"{t}\t{why}\n")

    keep = set(csv['Ticker'])
    cache = os.path.join(CACHE_DIR, f'daily_{PERIOD}.pkl')
    with open(cache, 'wb') as f:
        pickle.dump({'downloaded': datetime.now(), 'period': PERIOD,
                     'prices': {t: df for t, df in progress['data'].items() if t in keep},
                     'overseas': {r['Ticker']: r['Country'] for r in new_rows}}, f)
    os.remove(PROGRESS_FILE)

    log(f"\nDone. 5000.csv: {len(tickers)} → {len(csv)} tickers "
        f"(-{len(removed)} delisted, +{len(new_rows)} overseas, {len(progress['unchecked'])} unchecked kept)")
    if new_rows:
        log(pd.Series([r['Country'] for r in new_rows]).value_counts().to_string())
    log(f"Price cache: {cache}")


def redo_overseas():
    """Step 3 only: swap the previously-added overseas tickers for a fresh pick,
    reusing data_cache/daily_<period>.pkl for everything else."""
    today = pd.Timestamp(datetime.now().date())
    cache_path = os.path.join(CACHE_DIR, f'daily_{PERIOD}.pkl')
    with open(cache_path, 'rb') as f:
        cache = pickle.load(f)
    old = set(cache.get('overseas', {}))

    csv = pd.read_csv(TICKER_FILE)
    csv = csv[~csv['Ticker'].isin(old)]
    log(f"Replacing {len(old)} previously added overseas tickers ({len(csv)} others kept)")

    have = set(csv['Ticker'])
    seen_names = set(csv['Company'].map(norm_name))
    new_rows = pick_overseas(have, seen_names)

    progress = {'data': {t: df for t, df in cache['prices'].items() if t not in old},
                'missing': set(), 'no_data': {}, 'done': set(), 'unchecked': set()}
    reuse = {t: cache['prices'][t] for t in old if t in cache['prices']}
    progress['data'].update({r['Ticker']: reuse[r['Ticker']] for r in new_rows if r['Ticker'] in reuse})
    progress['done'].update(reuse)
    fetch([r['Ticker'] for r in new_rows], progress, 'overseas')
    verify(progress, 'overseas')
    new_rows = [r for r in new_rows if r['Ticker'] in progress['data']
                and (today - progress['data'][r['Ticker']].index[-1]).days <= DELIST_DAYS]

    csv = pd.concat([csv, pd.DataFrame(new_rows)[['Ticker', 'Company', 'Sector']]], ignore_index=True)
    csv.to_csv(TICKER_FILE, index=False)
    keep = set(csv['Ticker'])
    with open(cache_path, 'wb') as f:
        pickle.dump({'downloaded': cache['downloaded'], 'period': PERIOD,
                     'prices': {t: df for t, df in progress['data'].items() if t in keep},
                     'overseas': {r['Ticker']: r['Country'] for r in new_rows}}, f)
    if os.path.exists(PROGRESS_FILE):
        os.remove(PROGRESS_FILE)

    dropped = sorted(old - {r['Ticker'] for r in new_rows})
    log(f"\nDone. 5000.csv now {len(csv)} tickers, {len(new_rows)} overseas "
        f"(dropped {len(dropped)} earlier picks: {', '.join(dropped)})")
    log(pd.Series([r['Country'] for r in new_rows]).value_counts().to_string())


if __name__ == '__main__':
    main()
