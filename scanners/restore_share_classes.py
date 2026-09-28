"""
RESTORE SHARE-CLASS TICKERS
===========================
Old 5000.csv rows wrote class shares without a separator (BRKB, BFB, LENB).
Yahoo needs BRK-B / BF-B / LEN-B, so refresh_universe.py correctly found "no
data" for them and removed them — even though the companies are alive.

For every removed ticker shaped like <root><A|B|C|K>, this tries the dashed
symbol; if it has current prices it goes back into 5000.csv under the dashed
ticker (company / sector from the original row) and into the price cache.

Usage:
    python restore_share_classes.py
"""

import os
import re
import pickle
import subprocess
from io import StringIO
from datetime import datetime

import pandas as pd
import yfinance as yf

HERE        = os.path.dirname(os.path.abspath(__file__))
TICKER_FILE = os.path.join(HERE, 'CSV', '5000.csv')
REMOVED_LOG = os.path.join(HERE, 'CSV', 'removed_tickers.txt')
CACHE       = os.path.join(HERE, 'data_cache', 'daily_3y.pkl')
CLASS_SHAPE = re.compile(r'^([A-Z]{1,5})([ABCK])$')
FRESH_DAYS  = 30


def main():
    removed = [line.split('\t')[0] for line in open(REMOVED_LOG, encoding='utf-8')
               if line.strip() and not line.startswith('#')]
    # company / sector as they were before the refresh (the committed version)
    original = pd.read_csv(StringIO(subprocess.run(
        ['git', 'show', 'HEAD:scanners/CSV/5000.csv'], capture_output=True, text=True,
        cwd=HERE, encoding='utf-8').stdout)).drop_duplicates('Ticker').set_index('Ticker')

    csv = pd.read_csv(TICKER_FILE)
    with open(CACHE, 'rb') as f:
        cache = pickle.load(f)
    today = pd.Timestamp(datetime.now().date())

    restored = []
    for t in removed:
        m = CLASS_SHAPE.match(t)
        if not m or t not in original.index:
            continue
        dashed = f"{m.group(1)}-{m.group(2)}"
        if dashed in set(csv['Ticker']):
            continue
        h = yf.Ticker(dashed).history(period=cache['period'], auto_adjust=False)
        if not len(h) or (today - h.index[-1].tz_localize(None)).days > FRESH_DAYS:
            continue
        df = h[['Open', 'High', 'Low', 'Close', 'Volume']].dropna(subset=['Close'])
        df.columns = ['open', 'high', 'low', 'close', 'volume']
        df.index = df.index.tz_localize(None).normalize()
        cache['prices'][dashed] = df
        restored.append({'Ticker': dashed, 'Company': original.loc[t, 'Company'],
                         'Sector': original.loc[t, 'Sector'], 'was': t})
        print(f"  {t:<7} → {dashed:<8} {original.loc[t, 'Company']}")

    if restored:
        csv = pd.concat([csv, pd.DataFrame(restored)[['Ticker', 'Company', 'Sector']]], ignore_index=True)
        csv.to_csv(TICKER_FILE, index=False)
        with open(CACHE, 'wb') as f:
            pickle.dump(cache, f)
        with open(REMOVED_LOG, 'a', encoding='utf-8') as f:
            f.write(f"# restore_share_classes.py {datetime.now():%Y-%m-%d %H:%M} — "
                    f"{len(restored)} re-added under Yahoo's dashed symbol\n")
            for r in restored:
                f.write(f"{r['was']}\trestored as {r['Ticker']}\n")
    print(f"Restored {len(restored)} share-class tickers — 5000.csv now {len(csv)} tickers")


if __name__ == '__main__':
    main()
