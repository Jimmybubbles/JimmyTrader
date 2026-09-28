"""
RANGE 0-3-6-9-1 SCANNER (the 6 as the mean)
===========================================
Splits each stock's dollar range into the 0 - 3 - 6 - 9 - 1 levels
(0%, 30%, 60%, 90%, 100% of the range) and finds stocks whose daily price
action is rotating around the 6 — i.e. the 60% level is acting as the
"mean" price keeps coming back to, with the 3 and the 9 acting as the
outer bands it bounces between.

Dollar range = the same tiers as the fader / Range Level scanners
(db_fader_scanner.get_range_info): $1 ranges under $10, $10 ranges
$10–99, $50 ranges $100–499, $100 ranges $500+.
  e.g. a $14.20 stock sits in the $10–20 range → 3 = $13, 6 = $16, 9 = $19.

Signal criteria (all must pass, over the last LOOKBACK daily bars):
  - Every bar is measured against the CURRENT close's dollar range
  - Average close sits within MEAN_TOLERANCE points of the 6 (60%)
  - Close has crossed the 6 at least MIN_CROSSES times (it's a pivot,
    not a level price just passed through once)
  - At least MIN_IN_BAND_PCT of closes are between the 3 and the 9
  - Current close is between the 3 and the 9

Scoring (max ~14):
  - Crosses of the 6        +1 each (max 6)
  - Mean tightness          within 3 pts of 60 = +2, within 5 = +1
  - Time in 3–9 band        100% = +2, 90%+ = +1
  - Bars trading through 6  40%+ of bars = +2, 25%+ = +1
  - Edges held              +1 for a tag of the 3 that closed back above it,
                            +1 for a tag of the 9 that closed back below it

Setup (where price is vs the 6 right now):
  BELOW 6  — in the 3–5 zone, reversion target is up to the 6
  AT 6     — sitting on the mean
  ABOVE 6  — in the 7–9 zone, reversion target is back down to the 6
"""

import pandas as pd
import os
import sys
import json
from datetime import datetime

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, BASE_DIR)
from db_hammer_scanner import get_connection, get_all_tickers, get_ticker_daily
from db_fader_scanner import get_range_info

RESULTS_FILE     = os.path.join(BASE_DIR, 'last_range369_results.json')
LOOKBACK         = 30     # daily bars measured against the 6
MEAN_TOLERANCE   = 8.0    # avg close must be within this many range-points of 60
MIN_CROSSES      = 3      # closes must flip sides of the 6 at least this often
MIN_IN_BAND_PCT  = 80.0   # % of closes that must sit between the 3 and the 9
MIN_PRICE        = 1.0    # skip sub-$1 stocks
EDGE_ZONE        = 3.0    # within this many points of the 3 / 9 counts as a tag
AT_6_ZONE        = 5.0    # within this many points of 60 = "AT 6"

LEVELS = (0, 30, 60, 90, 100)


def levels_369(price):
    """Dollar range for `price` with the 0-3-6-9-1 levels in dollars."""
    rng = get_range_info(price)
    if not rng:
        return None
    low, size = rng['range_low'], rng['range_size']
    return {
        'range_low':  low,
        'range_size': size,
        **{f'L{p}': round(low + size * p / 100, 4) for p in LEVELS},
    }


def analyse(df):
    """Return a result dict if the last LOOKBACK bars rotate around the 6, else None."""
    win = df.iloc[-LOOKBACK:]
    price = float(win['close'].iloc[-1])
    lv = levels_369(price)
    if not lv:
        return None
    low, size = lv['range_low'], lv['range_size']

    def pos(s):
        return (s.astype(float) - low) / size * 100

    close_pos = pos(win['close'])
    high_pos  = pos(win['high'])
    low_pos   = pos(win['low'])

    cur_pos = float(close_pos.iloc[-1])
    if not (30 <= cur_pos <= 90):
        return None

    mean_pos = float(close_pos.mean())
    if abs(mean_pos - 60) > MEAN_TOLERANCE:
        return None

    side = (close_pos - 60).apply(lambda d: 1 if d > 0 else (-1 if d < 0 else 0))
    side = side[side != 0]
    crosses = int((side != side.shift()).sum() - 1) if len(side) else 0
    if crosses < MIN_CROSSES:
        return None

    in_band_pct = float(((close_pos >= 30) & (close_pos <= 90)).mean() * 100)
    if in_band_pct < MIN_IN_BAND_PCT:
        return None

    through_6_pct = float(((low_pos <= 60) & (high_pos >= 60)).mean() * 100)
    held_3 = bool(((low_pos <= 30 + EDGE_ZONE) & (close_pos > 30)).any())
    held_9 = bool(((high_pos >= 90 - EDGE_ZONE) & (close_pos < 90)).any())

    score = min(crosses, 6)
    dev = abs(mean_pos - 60)
    if dev <= 3:   score += 2
    elif dev <= 5: score += 1
    if in_band_pct >= 100:  score += 2
    elif in_band_pct >= 90: score += 1
    if through_6_pct >= 40:   score += 2
    elif through_6_pct >= 25: score += 1
    score += int(held_3) + int(held_9)

    if cur_pos < 60 - AT_6_ZONE:
        setup = 'BELOW 6'
    elif cur_pos > 60 + AT_6_ZONE:
        setup = 'ABOVE 6'
    else:
        setup = 'AT 6'

    return {
        'price':         round(price, 4),
        'position_pct':  round(cur_pos, 1),
        'setup':         setup,
        'mean_pos':      round(mean_pos, 1),
        'crosses':       crosses,
        'in_band_pct':   round(in_band_pct, 1),
        'through_6_pct': round(through_6_pct, 1),
        'held_3':        held_3,
        'held_9':        held_9,
        'to_6_pct':      round((lv['L60'] - price) / price * 100, 2),
        'score':         score,
        **lv,
    }


def run_range369_scan(log_callback=None):
    def log(msg):
        print(msg)
        if log_callback:
            log_callback(msg + '\n')

    log('=' * 60)
    log('RANGE 0-3-6-9-1 SCANNER (6 as the mean)')
    log('=' * 60)
    log(f"Started: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    log(f"Last {LOOKBACK} daily bars · mean within {MEAN_TOLERANCE:g} pts of the 6 · "
        f"{MIN_CROSSES}+ crosses · {MIN_IN_BAND_PCT:g}%+ closes between 3 and 9\n")

    conn = get_connection()
    tickers = get_all_tickers(conn)
    log(f"Scanning {len(tickers)} tickers...\n")

    all_results = []
    errors = 0

    for i, ticker in enumerate(tickers, 1):
        try:
            df = get_ticker_daily(conn, ticker)
            if df is None or len(df) < LOOKBACK or float(df['close'].iloc[-1]) < MIN_PRICE:
                continue

            r = analyse(df)
            if r:
                r['ticker'] = ticker
                r['date']   = df.index[-1].strftime('%Y-%m-%d')
                all_results.append(r)
                log(f"[{i}/{len(tickers)}] {ticker} {r['setup']} @ {r['position_pct']}% "
                    f"mean {r['mean_pos']} crosses {r['crosses']} score {r['score']}")

        except Exception as e:
            errors += 1
            if errors <= 10:
                log(f"[{i}/{len(tickers)}] {ticker}: ERROR — {str(e)[:60]}")

        # Reconnect every 300 tickers
        if i % 300 == 0:
            conn.close()
            conn = get_connection()
            log(f"\n--- Reconnected at ticker {i} ---\n")

    conn.close()

    all_results.sort(key=lambda x: x['score'], reverse=True)

    output = {
        'scan_date':       datetime.now().strftime('%Y-%m-%d %H:%M'),
        'total':           len(all_results),
        'tickers_scanned': len(tickers),
        'errors':          errors,
        'results':         all_results,
    }

    with open(RESULTS_FILE, 'w') as f:
        json.dump(output, f)

    log(f"\n{'='*60}")
    log(f"COMPLETE — {len(all_results)} stocks rotating around the 6 across {len(tickers)} tickers")
    log(f"Errors: {errors}")
    log('=' * 60)
    return output


def load_last_range369_results():
    if os.path.exists(RESULTS_FILE):
        with open(RESULTS_FILE) as f:
            return json.load(f)
    return None


if __name__ == '__main__':
    run_range369_scan()
