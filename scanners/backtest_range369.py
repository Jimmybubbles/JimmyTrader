"""
BACKTEST — Range 0-3-6-9-1 scanner (6 as the mean)
==================================================
Walks the live scanner rule (website/db_range369_scanner.analyse) forward day
by day over a sample of US stocks and trades the reversion back to the 6:

  BELOW 6 signal → LONG  next day's open, target = the 6, stop = just under the 3
  ABOVE 6 signal → SHORT next day's open, target = the 6, stop = just over the 9
  AT 6           → no trade (already at the mean)

  - Levels are frozen at the signal bar
  - Stop / target checked on each bar's high/low; if both hit the same bar,
    the stop is assumed first (conservative); gaps fill at the open
  - Time stop: exit at the close after MAX_HOLD bars
  - Skipped if the next open has already gapped past the target or stop
  - One position per ticker at a time
  - Every trade is sized at $10,000 (same as Jimmy's Ideas)

"Edge" compares each trade against that ticker's own average return over the
same number of days from ANY day, i.e. did the signal beat just being in the
stock (or short it) for that long?

Prices: yfinance daily, raw (not dividend-adjusted) so the dollar levels
match what the live scanner and TradingView show.

Usage:
    python backtest_range369.py                         # 200 random tickers, 3 years
    python backtest_range369.py --sample 0 --longs-only # every ticker in 5000.csv, BELOW 6 only
    python backtest_range369.py --period 5y

If data_cache/daily_<period>.pkl exists (written by refresh_universe.py) prices
come from there instead of being downloaded again.
"""

import os
import sys
import pickle
import random
import argparse
from datetime import datetime

import pandas as pd
import yfinance as yf

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'website'))

try:
    import db_config  # noqa: F401  (only needed on the server)
except ImportError:
    import types
    _cfg = types.ModuleType('db_config')
    for _k in ('DB_HOST', 'DB_USER', 'DB_PASSWORD', 'DB_NAME'):
        setattr(_cfg, _k, '')
    _cfg.DB_PORT = 3306
    sys.modules['db_config'] = _cfg

from db_range369_scanner import (analyse, levels_369, LOOKBACK, MIN_PRICE, MEAN_TOLERANCE,
                                 MIN_CROSSES, MIN_IN_BAND_PCT, EDGE_ZONE, AT_6_ZONE)

TICKER_FILE = os.path.join(HERE, 'CSV', '5000.csv')
CACHE_DIR   = os.path.join(HERE, 'data_cache')

_ap = argparse.ArgumentParser()
_ap.add_argument('--sample', type=int, default=200, help='random tickers to test, 0 = all')
_ap.add_argument('--period', default='3y')
_ap.add_argument('--longs-only', action='store_true', help='only trade BELOW 6 signals')
ARGS = _ap.parse_args()

SAMPLE      = ARGS.sample
PERIOD      = ARGS.period
LONGS_ONLY  = ARGS.longs_only
OUT_FILE    = os.path.join(HERE, 'range369_backtest' + ('_longs' if LONGS_ONLY else '') + '.txt')
SEED        = 369
MAX_HOLD    = 20
STAKE       = 10_000


def load_prices(tickers):
    cache = os.path.join(CACHE_DIR, f'daily_{PERIOD}.pkl')
    if os.path.exists(cache):
        with open(cache, 'rb') as f:
            cached = pickle.load(f)['prices']
        print(f"Using cached prices: {cache}")
        return {t: cached[t][['open', 'high', 'low', 'close']] for t in tickers
                if t in cached and len(cached[t]) >= LOOKBACK + MAX_HOLD + 5}
    raw = yf.download(tickers, period=PERIOD, interval='1d', auto_adjust=False,
                      group_by='ticker', progress=False, threads=True)
    out = {}
    for t in tickers:
        try:
            df = raw[t][['Open', 'High', 'Low', 'Close']].dropna()
        except KeyError:
            continue
        df.columns = ['open', 'high', 'low', 'close']
        if len(df) >= LOOKBACK + MAX_HOLD + 5:
            out[t] = df
    return out


def baseline_returns(df):
    """Mean h-day forward return (next open → close h bars later) for h = 1..MAX_HOLD."""
    o, c = df['open'], df['close']
    return {h: float((c.shift(-h) / o.shift(-1) - 1).mean() * 100) for h in range(1, MAX_HOLD + 1)}


def backtest_ticker(ticker, df):
    trades, skipped = [], 0
    o, h, l, c = (df[k].to_numpy() for k in ('open', 'high', 'low', 'close'))
    dates = df.index
    base = baseline_returns(df)
    t = LOOKBACK - 1
    while t < len(df) - 2:
        # Cheap numpy pre-check of analyse()'s own mean / band tests — only bars
        # that pass it reach the full (slower, pandas) scanner rule
        lv = levels_369(c[t]) if c[t] >= MIN_PRICE else None
        if lv:
            w = (c[t - LOOKBACK + 1:t + 1] - lv['range_low']) / lv['range_size'] * 100
            hi = 60 - AT_6_ZONE if LONGS_ONLY else 90
            if not (30 <= w[-1] <= hi) or abs(w.mean() - 60) > MEAN_TOLERANCE:
                lv = None
        if not lv:
            t += 1
            continue
        sig = analyse(df.iloc[:t + 1])
        if not sig or sig['setup'] == 'AT 6' or (LONGS_ONLY and sig['setup'] == 'ABOVE 6'):
            t += 1
            continue

        long_ = sig['setup'] == 'BELOW 6'
        size, low = sig['range_size'], sig['range_low']
        target = sig['L60']
        stop = low + size * ((30 - EDGE_ZONE) if long_ else (90 + EDGE_ZONE)) / 100
        e = t + 1
        entry = o[e]
        if (long_ and (entry >= target or entry <= stop)) or \
           (not long_ and (entry <= target or entry >= stop)):
            skipped += 1
            t += 1
            continue

        exit_px, why, x = None, 'time', e
        for x in range(e, min(e + MAX_HOLD, len(df))):
            if long_:
                if l[x] <= stop:
                    exit_px, why = min(o[x], stop) if x > e else stop, 'stop'
                elif h[x] >= target:
                    exit_px, why = max(o[x], target) if x > e else target, 'target'
            else:
                if h[x] >= stop:
                    exit_px, why = max(o[x], stop) if x > e else stop, 'stop'
                elif l[x] <= target:
                    exit_px, why = min(o[x], target) if x > e else target, 'target'
            if exit_px is not None:
                break
        if exit_px is None:
            exit_px = c[x]

        held = x - e + 1
        ret = (exit_px / entry - 1) * 100 * (1 if long_ else -1)
        b = base[held] * (1 if long_ else -1)
        trades.append({
            'ticker': ticker, 'side': 'LONG' if long_ else 'SHORT', 'score': sig['score'],
            'signal_date': dates[t].strftime('%Y-%m-%d'), 'exit_date': dates[x].strftime('%Y-%m-%d'),
            'entry': entry, 'exit': exit_px, 'target': target, 'stop': stop,
            'pos': sig['position_pct'], 'crosses': sig['crosses'],
            'held': held, 'why': why, 'ret': ret, 'edge': ret - b,
            'pnl': STAKE * ret / 100,
        })
        t = x + 1
    return trades, skipped


def stats(trades):
    if not trades:
        return None
    r = pd.Series([t['ret'] for t in trades])
    wins, losses = r[r > 0], r[r <= 0]
    gross_loss = -losses.sum()
    return {
        'n': len(r), 'win': len(wins) / len(r) * 100, 'avg': r.mean(), 'med': r.median(),
        'avg_win': wins.mean() if len(wins) else 0.0, 'avg_loss': losses.mean() if len(losses) else 0.0,
        'pf': wins.sum() / gross_loss if gross_loss > 0 else float('inf'),
        'held': sum(t['held'] for t in trades) / len(r),
        'edge': sum(t['edge'] for t in trades) / len(r),
        'pnl': sum(t['pnl'] for t in trades),
        'exits': {k: sum(1 for t in trades if t['why'] == k) for k in ('target', 'stop', 'time')},
    }


def stats_block(title, trades):
    s = stats(trades)
    if not s:
        return [f"{title}: no trades", '']
    ex = s['exits']
    return [
        title,
        '-' * len(title),
        f"  Trades        {s['n']}",
        f"  Win rate      {s['win']:.1f}%",
        f"  Avg return    {s['avg']:+.2f}%   (median {s['med']:+.2f}%)",
        f"  Avg win/loss  {s['avg_win']:+.2f}% / {s['avg_loss']:+.2f}%",
        f"  Profit factor {s['pf']:.2f}",
        f"  Avg hold      {s['held']:.1f} days",
        f"  Exits         target {ex['target']} · stop {ex['stop']} · time {ex['time']}",
        f"  Edge vs stock {s['edge']:+.2f}% per trade (vs just holding that stock the same # of days)",
        f"  P&L @ $10k    ${s['pnl']:+,.0f}",
        '',
    ]


def main():
    started = datetime.now()
    universe = pd.read_csv(TICKER_FILE)['Ticker'].dropna().astype(str)
    universe = list(dict.fromkeys(universe))
    sample = sorted(random.Random(SEED).sample(universe, SAMPLE) if 0 < SAMPLE < len(universe) else universe)
    print(f"Downloading {len(sample)} tickers ({PERIOD})...")
    prices = load_prices(sample)
    print(f"Got usable data for {len(prices)}. Backtesting...")

    all_trades, skipped, signal_tickers = [], 0, 0
    for i, (tk, df) in enumerate(sorted(prices.items()), 1):
        tr, sk = backtest_ticker(tk, df)
        all_trades += tr
        skipped += sk
        signal_tickers += bool(tr)
        print(f"  [{i}/{len(prices)}] {tk}: {len(tr)} trades")

    longs  = [t for t in all_trades if t['side'] == 'LONG']
    shorts = [t for t in all_trades if t['side'] == 'SHORT']
    first = min(df.index[0] for df in prices.values()).date()
    last  = max(df.index[-1] for df in prices.values()).date()

    L = [
        '=' * 78,
        'RANGE 0-3-6-9-1 BACKTEST  (6 as the mean)',
        '=' * 78,
        f"Run:        {started:%Y-%m-%d %H:%M}",
        f"Universe:   {len(sample)} " + ("random " if 0 < SAMPLE < len(universe) else "") +
        f"tickers from 5000.csv (seed {SEED}), "
        f"{len(prices)} with enough data",
        f"Period:     {first} → {last} ({PERIOD} daily, yfinance raw prices)",
        f"Signal:     last {LOOKBACK} bars, mean within {MEAN_TOLERANCE:g} pts of 6, "
        f"{MIN_CROSSES}+ crosses, {MIN_IN_BAND_PCT:g}%+ closes in 3–9 band",
        ("Trade:      LONGS ONLY — BELOW 6 → long (ABOVE 6 shorts omitted), next open; target the 6; "
         if LONGS_ONLY else "Trade:      BELOW 6 → long, ABOVE 6 → short, next open; target the 6; ") +
        f"stop {EDGE_ZONE:g} pts past the 3/9; max {MAX_HOLD} days",
        f"Tickers that produced a trade: {signal_tickers}   ·   "
        f"signals skipped (gapped past target/stop): {skipped}",
        '',
    ]
    L += stats_block('ALL TRADES', all_trades)
    L += stats_block('LONGS  (BELOW 6 → up to the 6)', longs)
    if not LONGS_ONLY:
        L += stats_block('SHORTS (ABOVE 6 → down to the 6)', shorts)

    L += ['BY MARKET  (ticker suffix: none = US)', '-' * 37]
    by_mkt = {}
    for t in all_trades:
        by_mkt.setdefault('.' + t['ticker'].rsplit('.', 1)[1] if '.' in t['ticker'] else 'US', []).append(t)
    for mkt, tr in sorted(by_mkt.items(), key=lambda x: -len(x[1])):
        s = stats(tr)
        L.append(f"  {mkt:<5} {s['n']:>6} trades  win {s['win']:5.1f}%  avg {s['avg']:+6.2f}%  "
                 f"PF {s['pf']:5.2f}  edge {s['edge']:+6.2f}%  P&L ${s['pnl']:+,.0f}")
    L.append('')

    now = []
    for tk, df in prices.items():
        sig = analyse(df)
        if sig and (sig['setup'] == 'BELOW 6' or (not LONGS_ONLY and sig['setup'] == 'ABOVE 6')):
            now.append((tk, df.index[-1].strftime('%Y-%m-%d'), sig))
    now.sort(key=lambda x: -x[2]['score'])
    L += [f"SIGNALS ON THE LATEST BAR  ({len(now)} — what the scanner would show today)", '-' * 60,
          f"  {'Ticker':<10}{'Date':<11}{'Setup':<9}{'Sc':>3}{'Price':>10}{'3':>9}{'6':>9}{'9':>9}"
          f"{'In rng':>8}{'X':>3}{'To 6':>8}"]
    for tk, d, g in now:
        L.append(f"  {tk:<10}{d:<11}{g['setup']:<9}{g['score']:>3}{g['price']:>10.2f}{g['L30']:>9.2f}"
                 f"{g['L60']:>9.2f}{g['L90']:>9.2f}{g['position_pct']:>7.1f}%{g['crosses']:>3}{g['to_6_pct']:>+7.1f}%")
    L.append('')

    L += ['BY SCORE', '--------']
    for lo, hi, name in ((0, 6, 'score 0-6 '), (7, 9, 'score 7-9 '), (10, 99, 'score 10+ ')):
        s = stats([t for t in all_trades if lo <= t['score'] <= hi])
        if s:
            L.append(f"  {name} {s['n']:>5} trades  win {s['win']:5.1f}%  avg {s['avg']:+6.2f}%  "
                     f"PF {s['pf']:5.2f}  edge {s['edge']:+6.2f}%")
    L.append('')

    L += ['BY ENTRY POSITION IN RANGE (how far from the 6 at the signal)', '-' * 62]
    buckets = ((30, 45, 'long  from 30-45%'), (45, 55, 'long  from 45-55%'),
               (65, 75, 'short from 65-75%'), (75, 90.1, 'short from 75-90%'))
    for lo, hi, name in buckets:
        s = stats([t for t in all_trades if lo <= t['pos'] < hi])
        if s:
            L.append(f"  {name}  {s['n']:>5} trades  win {s['win']:5.1f}%  avg {s['avg']:+6.2f}%  "
                     f"PF {s['pf']:5.2f}")
    L.append('')

    by_tk = {}
    for t in all_trades:
        by_tk.setdefault(t['ticker'], []).append(t)
    tk_rows = sorted(((tk, stats(tr)) for tk, tr in by_tk.items()), key=lambda x: x[1]['pnl'], reverse=True)
    L += ['PER TICKER  (sorted by P&L @ $10k per trade)', '-' * 44,
          f"  {'Ticker':<8}{'Trades':>7}{'Win%':>8}{'Avg%':>9}{'P&L':>11}"]
    for tk, s in tk_rows:
        L.append(f"  {tk:<8}{s['n']:>7}{s['win']:>8.1f}{s['avg']:>+9.2f}{s['pnl']:>+11,.0f}")
    L.append('')

    L += ['ALL TRADES', '----------',
          f"  {'Ticker':<7}{'Side':<6}{'Sc':>3} {'Signal':<11}{'Exit':<11}{'Entry':>9}{'Target':>9}"
          f"{'Stop':>9}{'Exit$':>9}{'Days':>5} {'Why':<7}{'Ret%':>7}"]
    for t in sorted(all_trades, key=lambda t: (t['signal_date'], t['ticker'])):
        L.append(f"  {t['ticker']:<7}{t['side']:<6}{t['score']:>3} {t['signal_date']:<11}{t['exit_date']:<11}"
                 f"{t['entry']:>9.2f}{t['target']:>9.2f}{t['stop']:>9.2f}{t['exit']:>9.2f}"
                 f"{t['held']:>5} {t['why']:<7}{t['ret']:>+7.2f}")

    with open(OUT_FILE, 'w', encoding='utf-8') as f:
        f.write('\n'.join(L) + '\n')
    print('\n'.join(L[:60]))
    print(f"\nFull report → {OUT_FILE}  ({(datetime.now() - started).seconds}s)")


if __name__ == '__main__':
    main()
