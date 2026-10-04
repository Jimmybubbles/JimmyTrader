"""
SECTOR / INDUSTRY ROTATION (Relative Rotation Graph)
====================================================
Shows where money is rotating: sector ETFs vs SPY, industry ETFs vs SPY, and
the stocks inside an industry vs that industry's ETF.

RRG maths (open approximation of JdK RS-Ratio / RS-Momentum, weekly bars):
  rs        = EMA(SMOOTH) of 100 × price / benchmark
  RS-Ratio  = 100 + 2 × z-score of rs over WINDOW bars  (>100 = beating the benchmark)
  RS-Mom    = 100 + 2 × (RS-Ratio change over MOM_BARS) / its WINDOW std
                                                        (>100 = relative strength rising)
Quadrants rotate clockwise: Improving → Leading → Weakening → Lagging.

Stocks → industry: each US stock is assigned to the industry ETF its daily
returns correlated with most over the last year (min MIN_CORR, a small bonus
for ETFs in the stock's own sector), else to its sector ETF. That's "what it
trades with" — the stocks that actually move when money flows into the ETF.
The assignment is rebuilt by the admin job (run_rotation_job) and saved to
last_rotation_results.json; the RRGs themselves are computed live from the DB.

Usage:
    python db_rotation.py      # rebuild stock → industry assignment
"""

import os
import sys
import json
from datetime import datetime, timedelta

import numpy as np
import pandas as pd

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, BASE_DIR)

RESULTS_FILE = os.path.join(BASE_DIR, 'last_rotation_results.json')
TICKER_FILE  = os.path.join(BASE_DIR, 'CSV', '5000.csv')

BENCH        = 'SPY'
WINDOW       = 26        # bars of history the RS-Ratio / RS-Momentum are scored against
SMOOTH       = 4         # EMA span applied to the relative-strength line first
MOM_BARS     = 4         # RS-Momentum = change in RS-Ratio over this many bars
DAILY        = {'window': 50, 'smooth': 5, 'mom_bars': 5}   # same idea on daily bars
TAIL         = 8         # tail points shown per dot
CORR_DAYS    = 250       # daily bars used for the stock → ETF correlation
MIN_CORR     = 0.5
SECTOR_BONUS = 0.05      # tie-break towards an industry ETF in the stock's own sector
MIN_DOLLAR_VOL = 2_000_000   # stocks below this avg daily $ volume are left off the drill-down

# Sector ETF → (name, [(industry ETF, name), ...]). Industry ETFs are the
# liquid (≥ ~$10M/day) ones for each sector, without near-duplicates.
SECTORS = {
    'XLK':  ('Technology',          [('SMH', 'Semiconductors'), ('IGV', 'Software'),
                                     ('CIBR', 'Cybersecurity'), ('SKYY', 'Cloud Computing')]),
    'XLF':  ('Financials',          [('KBE', 'Banks'), ('KRE', 'Regional Banks'), ('KIE', 'Insurance'),
                                     ('IAI', 'Brokers & Exchanges'), ('BLOK', 'Crypto / Blockchain')]),
    'XLE':  ('Energy',              [('XOP', 'Oil & Gas E&P'), ('OIH', 'Oil Services'),
                                     ('AMLP', 'Pipelines (MLPs)'), ('FCG', 'Natural Gas'), ('URA', 'Uranium')]),
    'XLV':  ('Healthcare',          [('XBI', 'Biotech'), ('IHI', 'Medical Devices'),
                                     ('IHF', 'Healthcare Providers'), ('XPH', 'Pharma')]),
    'XLI':  ('Industrials',         [('ITA', 'Aerospace & Defense'), ('JETS', 'Airlines'), ('IYT', 'Transports'),
                                     ('PAVE', 'Infrastructure'), ('BOTZ', 'Robotics & AI')]),
    'XLY':  ('Cons. Discretionary', [('ITB', 'Homebuilders'), ('XRT', 'Retail'), ('FDN', 'Internet'),
                                     ('PEJ', 'Leisure & Travel')]),
    'XLC':  ('Communications',      [('IYZ', 'Telecom')]),
    'XLP':  ('Cons. Staples',       [('MOO', 'Agribusiness')]),
    'XLRE': ('Real Estate',         []),
    'XLU':  ('Utilities',           [('ICLN', 'Clean Energy'), ('TAN', 'Solar'), ('NLR', 'Nuclear'),
                                     ('GRID', 'Grid Infrastructure')]),
    'XLB':  ('Materials',           [('XME', 'Metals & Mining'), ('GDX', 'Gold Miners'),
                                     ('GDXJ', 'Junior Gold Miners'), ('COPX', 'Copper Miners'),
                                     ('LIT', 'Lithium & Battery'), ('REMX', 'Rare Earths')]),
}
INDUSTRY_SECTOR = {etf: sec for sec, (_, inds) in SECTORS.items() for etf, _ in inds}
NAMES = {**{sec: name for sec, (name, _) in SECTORS.items()},
         **{etf: name for _, (_, inds) in SECTORS.items() for etf, name in inds}, BENCH: 'S&P 500'}
ALL_ETFS = [BENCH] + list(SECTORS) + list(INDUSTRY_SECTOR)

# 5000.csv uses GICS names for US stocks and Yahoo names for the overseas ones
STOCK_SECTOR = {
    'Information Technology': 'XLK', 'Technology': 'XLK',
    'Financials': 'XLF', 'Financial Services': 'XLF',
    'Energy': 'XLE',
    'Health Care': 'XLV', 'Healthcare': 'XLV',
    'Industrials': 'XLI',
    'Consumer Discretionary': 'XLY', 'Consumer Cyclical': 'XLY',
    'Communication': 'XLC', 'Communication Services': 'XLC',
    'Consumer Staples': 'XLP', 'Consumer Defensive': 'XLP',
    'Real Estate': 'XLRE',
    'Utilities': 'XLU',
    'Materials': 'XLB', 'Basic Materials': 'XLB',
}

QUADRANTS = ('Leading', 'Weakening', 'Lagging', 'Improving')


# ── RRG maths ────────────────────────────────────────────────────────────────

def to_weekly(daily):
    """Daily closes (index = dates, columns = tickers) → Friday closes."""
    return daily.resample('W-FRI').last().dropna(how='all')


def rrg(closes, bench_col, window=WINDOW, smooth=SMOOTH, mom_bars=MOM_BARS):
    """RS-Ratio and RS-Momentum for every column in `closes` against `bench_col`.
    Returns (ratio, momentum) DataFrames aligned to `closes`.

    The relative-strength line is EMA-smoothed BEFORE it's scored — scoring raw
    week-to-week rs made dots leap across the chart (44% of tail steps reversed
    direction); smoothed, tails travel in arcs like a real RRG (17%)."""
    rs = 100 * closes.div(closes[bench_col], axis=0)
    rs = rs.ewm(span=smooth, adjust=False).mean()
    ratio = 100 + 2 * (rs - rs.rolling(window).mean()) / rs.rolling(window).std()
    change = ratio - ratio.shift(mom_bars)
    mom = 100 + 2 * change / change.rolling(window).std()
    return ratio.drop(columns=[bench_col]), mom.drop(columns=[bench_col])


def quadrant(r, m):
    if r >= 100:
        return 'Leading' if m >= 100 else 'Weakening'
    return 'Improving' if m >= 100 else 'Lagging'


def heading(points):
    """Compass arrow for the last tail segment — the direction the dot is travelling."""
    if len(points) < 2:
        return ''
    dx = points[-1][1] - points[-2][1]
    dy = points[-1][2] - points[-2][2]
    if abs(dx) < 1e-9 and abs(dy) < 1e-9:
        return '·'
    ang = (np.degrees(np.arctan2(dy, dx)) + 360) % 360
    return '→↗↑↖←↙↓↘'[int(((ang + 22.5) % 360) // 45)]


def pct(series, bars):
    s = series.dropna()
    if len(s) <= bars or s.iloc[-1 - bars] == 0:
        return None
    return round(float(s.iloc[-1] / s.iloc[-1 - bars] * 100 - 100), 2)


def rotation_rows(daily_close, daily_dollar_vol, tickers, bench, weekly=True, tail=TAIL):
    """One dict per ticker: tail points, quadrant, heading, returns and money-flow."""
    cols = [t for t in tickers if t in daily_close.columns] + [bench]
    closes = daily_close[cols].dropna(subset=[bench])
    bars = to_weekly(closes) if weekly else closes
    ratio, mom = rrg(bars, bench) if weekly else rrg(bars, bench, **DAILY)
    rows = []
    for t in cols[:-1]:
        pts = [(d.strftime('%Y-%m-%d'), round(float(r), 2), round(float(m), 2))
               for d, r, m in zip(ratio.index, ratio[t], mom[t]) if pd.notna(r) and pd.notna(m)][-tail:]
        if len(pts) < 2:
            continue
        r_now, m_now = pts[-1][1], pts[-1][2]
        q_prev = quadrant(pts[-2][1], pts[-2][2])
        dv = daily_dollar_vol[t].dropna() if t in daily_dollar_vol else pd.Series(dtype=float)
        flow = (round(float(dv.tail(20).mean() / dv.iloc[-150:-20].mean()), 2)
                if len(dv) >= 150 and dv.iloc[-150:-20].mean() > 0 else None)
        px = closes[t]
        rows.append({
            'ticker': t, 'name': NAMES.get(t, t), 'points': pts,
            'ratio': r_now, 'mom': m_now, 'quadrant': quadrant(r_now, m_now),
            'prev_quadrant': q_prev, 'heading': heading(pts),
            'r1w': pct(px, 5), 'r1m': pct(px, 21), 'r3m': pct(px, 63), 'r6m': pct(px, 126),
            'flow': flow,
            'dollar_vol': round(float(dv.tail(20).mean()), 0) if len(dv) else 0,
        })
    return rows


# ── Data access ──────────────────────────────────────────────────────────────

def get_connection():
    import pymysql
    from db_config import DB_HOST, DB_USER, DB_PASSWORD, DB_NAME, DB_PORT
    return pymysql.connect(host=DB_HOST, user=DB_USER, password=DB_PASSWORD,
                           database=DB_NAME, port=DB_PORT, charset='utf8mb4')


def load_daily(tickers, days):
    """(closes, dollar volume) wide DataFrames for `tickers` over the last `days` calendar days."""
    if not tickers:
        return pd.DataFrame(), pd.DataFrame()
    conn = get_connection()
    try:
        fmt = ','.join(['%s'] * len(tickers))
        with conn.cursor() as cur:
            cur.execute(f"""SELECT ticker, date, close, volume FROM prices
                            WHERE ticker IN ({fmt}) AND date >= %s ORDER BY date""",
                        [t.upper() for t in tickers] + [(datetime.now() - timedelta(days=days)).date()])
            rows = cur.fetchall()
    finally:
        conn.close()
    df = pd.DataFrame(rows, columns=['ticker', 'date', 'close', 'volume'])
    if df.empty:
        return pd.DataFrame(), pd.DataFrame()
    df['date'] = pd.to_datetime(df['date'])
    df['close'] = pd.to_numeric(df['close'], errors='coerce')
    df['dv'] = df['close'] * pd.to_numeric(df['volume'], errors='coerce')
    close = df.pivot_table(index='date', columns='ticker', values='close')
    dv = df.pivot_table(index='date', columns='ticker', values='dv')
    return close, dv


def ensure_etf_prices(log=print):
    """Make sure every rotation ETF has current history in the prices table — new
    industry ETFs (IGV, ITA, KIE…) aren't in 5000.csv so the daily update never adds them."""
    import yfinance as yf
    from db_daily_update import insert_rows
    conn = get_connection()
    try:
        fmt = ','.join(['%s'] * len(ALL_ETFS))
        with conn.cursor() as cur:
            cur.execute(f"SELECT ticker, MAX(date) FROM prices WHERE ticker IN ({fmt}) GROUP BY ticker", ALL_ETFS)
            last = {t: d for t, d in cur.fetchall()}
        today = datetime.now().date()
        for t in ALL_ETFS:
            d = last.get(t)
            if d and (today - d).days <= 1:
                continue
            start = (d + timedelta(days=1)) if d else today - timedelta(days=1825)
            df = yf.download(t, start=start, end=today + timedelta(days=1), auto_adjust=False,
                             progress=False)
            n = insert_rows(conn, t, df) if df is not None and len(df) else 0
            log(f"  {t}: {'+' + str(n) + ' rows' if n else 'up to date'}" + ('' if d else ' (new, 5y history)'))
    finally:
        conn.close()


def stock_sectors():
    """{ticker: sector ETF} for US stocks in 5000.csv (no suffix, not an ETF/index)."""
    csv = pd.read_csv(TICKER_FILE)
    out = {}
    for t, s in zip(csv['Ticker'].astype(str), csv['Sector'].astype(str)):
        if any(c in t for c in '.=^') or t in NAMES:
            continue
        if s in STOCK_SECTOR:
            out[t] = STOCK_SECTOR[s]
    return out


# ── Stock → industry assignment ─────────────────────────────────────────────

def assign_industries(daily_close, daily_dollar_vol, sectors):
    """{stock: {etf, sector, corr, beta, dollar_vol}} — the industry ETF each stock trades with."""
    rets = daily_close.pct_change(fill_method=None).iloc[-CORR_DAYS:]
    etfs = [e for e in INDUSTRY_SECTOR if e in rets.columns]
    sec_etfs = [s for s in SECTORS if s in rets.columns]
    out = {}
    for stock, sec in sectors.items():
        if stock not in rets.columns:
            continue
        pair = rets[[stock] + etfs + sec_etfs].dropna()
        if len(pair) < CORR_DAYS // 2:
            continue
        corr = pair.corr()[stock]
        scored = {e: corr[e] + (SECTOR_BONUS if INDUSTRY_SECTOR[e] == sec else 0) for e in etfs}
        best = max(scored, key=scored.get) if scored else None
        etf = best if best and corr[best] >= MIN_CORR else sec
        c = float(corr.get(etf, np.nan))
        beta = float(pair[stock].cov(pair[etf]) / pair[etf].var()) if etf in pair else None
        dv = daily_dollar_vol[stock].dropna().tail(20).mean() if stock in daily_dollar_vol else 0
        out[stock] = {'etf': etf, 'sector': sec, 'corr': round(c, 2) if pd.notna(c) else None,
                      'beta': round(beta, 2) if beta is not None and pd.notna(beta) else None,
                      'dollar_vol': round(float(dv), 0) if pd.notna(dv) else 0}
    return out


def run_rotation_job(log_callback=None):
    def log(msg):
        print(msg)
        if log_callback:
            log_callback(msg + '\n')

    log('=' * 60)
    log('ROTATION — update ETF prices + assign stocks to industries')
    log('=' * 60)
    log(f"Started: {datetime.now():%Y-%m-%d %H:%M:%S}\n")
    log(f"Checking {len(ALL_ETFS)} rotation ETFs in the prices table...")
    ensure_etf_prices(log)

    sectors = stock_sectors()
    log(f"\nLoading {len(sectors)} US stocks for the correlation assignment...")
    close, dv = load_daily(list(sectors) + ALL_ETFS, days=int(CORR_DAYS * 1.6))
    assigned = assign_industries(close, dv, sectors)

    counts = pd.Series([a['etf'] for a in assigned.values()]).value_counts()
    for etf in [e for s in SECTORS for e in [s] + [i for i, _ in SECTORS[s][1]]]:
        log(f"  {etf:<5} {NAMES[etf]:<22} {int(counts.get(etf, 0)):>4} stocks")

    output = {'scan_date': datetime.now().strftime('%Y-%m-%d %H:%M'),
              'total': len(assigned), 'tickers_scanned': len(sectors),
              'results': assigned}
    with open(RESULTS_FILE, 'w') as f:
        json.dump(output, f)
    log(f"\nCOMPLETE — {len(assigned)} stocks assigned to {counts.size} sector / industry ETFs")
    return output


def load_last_rotation_results():
    if os.path.exists(RESULTS_FILE):
        with open(RESULTS_FILE) as f:
            return json.load(f)
    return None


if __name__ == '__main__':
    run_rotation_job()
