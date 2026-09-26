"""
ASX/US Stock Data Manager - PythonAnywhere Web App
===================================================
Dashboard for managing stock data + Channel Finder Scanner + Charts.

PythonAnywhere WSGI setup:
  import sys
  sys.path.insert(0, '/home/JimmyTrader/watchlist_Scanner')
  from flask_app import app as application
"""

import os
import sys
import uuid
import threading
import subprocess
import json
import hmac
import hashlib
import math
import pandas as pd
from datetime import datetime

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
REPO_DIR = os.path.dirname(BASE_DIR)
sys.path.insert(0, BASE_DIR)

# Find the real Python executable (sys.executable is uwsgi inside the web app)
PYTHON = os.path.join(sys.prefix, 'bin', 'python3')
if not os.path.exists(PYTHON):
    PYTHON = os.path.join(sys.prefix, 'bin', 'python')

from flask import Flask, redirect, jsonify, request, Response, send_from_directory
import pymysql

from db_config import (DB_HOST, DB_USER, DB_PASSWORD, DB_NAME, DB_PORT, ADMIN_PASSWORD,
                       JANG_PASSWORD, HODAN_PASSWORD, SECRET_KEY, GITHUB_WEBHOOK_SECRET,
                       WSGI_RELOAD_FILE)
from db_channel_scanner import run_scan, load_last_results, get_connection, get_ticker_data
from db_fader_scanner import run_fader_scan, load_last_fader_results
from db_efi_scanner import run_efi_scan, load_last_efi_results
from db_wick_scanner import run_wick_scan, load_last_wick_results
from db_hammer_scanner import run_hammer_scan, load_last_hammer_results
from db_gapdown_scanner import run_gapdown_scan, load_last_gapdown_results
from db_marubozu_scanner import run_marubozu_scan, load_last_marubozu_results
from db_extreme_scanner import run_extreme_scan, load_last_extreme_results
from db_range_oscillator_scanner import run_range_oscillator_scan, load_last_range_oscillator_results
from db_swing_scanner import run_swing_scan, load_last_swing_results
from db_higher_low_scanner import run_higher_low_scan, load_last_higher_low_results
from db_extreme_exit_scanner import run_extreme_exit_scan, load_last_extreme_exit_results
from db_doublebottom_scanner import run_doublebottom_scan, load_last_doublebottom_results
from db_recession_watchlist import (
    run_recession_scan, load_last_recession_results,
    THEMES as RECESSION_THEMES, PILLARS as RECESSION_PILLARS,
    tradingview_symbol as RECESSION_TV_SYMBOL, tradingview_list as RECESSION_TV_LIST,
    NOSE_DIVE_PCT as RECESSION_NOSE_DIVE, APPROACH_PCT as RECESSION_APPROACH,
)
from db_price_channel_scanner import (
    run_price_channel_scan, load_last_price_channel_results,
    get_ticker_daily, resample_weekly, resample_monthly,
    find_pivot_highs, find_pivot_lows, fit_line, CONFIGS as PCHAN_CONFIGS,
)
from db_picks import (init_tables, get_account, get_positions, get_portfolio_value,
                      get_history, buy_stock, sell_stock, get_daily_changes,
                      get_closed_trades, add_manual_closed_trade, delete_closed_trade, UPLOADS_DIR,
                      STYLES)
from db_ideas import (init_tables as init_ideas_tables, post_idea, get_open_ideas,
                      get_closed_ideas, close_idea, delete_idea, get_system_summary,
                      IDEA_NOTIONAL)
from db_ask import (init_tables as init_ask_tables, register_user, login_user,
                    submit_question, answer_question, get_questions, get_username,
                    get_user_stats)
from db_dividend import (init_tables as init_dividend_tables, get_all_dividend_stocks,
                         get_dividend_stock, upsert_dividend_stock, delete_dividend_stock)
from db_asx import (init_tables as init_asx_tables, ASX_200,
                    get_asx_sparklines_batch, get_asx_latest_prices,
                    get_asx_chart_data, get_tickers_with_data,
                    get_asx_account, get_asx_picks, get_asx_history,
                    get_asx_portfolio_value, buy_asx_stock, sell_asx_stock,
                    get_asx_daily_changes, get_closed_asx_trades,
                    add_manual_closed_asx_trade, delete_closed_asx_trade)
from bs_pricing import bs_price_greeks, assumed_iv_for_price, strike_increment_for_price, effective_iv
from db_options_picks import (init_tables as init_options_tables,
                              get_options_account, get_options_positions,
                              get_options_portfolio_value, get_options_history,
                              buy_option, sell_option, reset_account as reset_options_account)
from db_options_tracker import (init_tables as init_tracker_tables,
                                create_tracker, get_trackers, delete_tracker,
                                build_tracker_rows)
from db_options_data import (init_tables as init_options_data_tables,
                             refresh_all_relevant_chains, lookup_chain_on_demand)
from flask import session

RESULTS_DIR = os.path.join(BASE_DIR, 'updated_Results_for_scan')
RANGE_RESULTS_FILE = os.path.join(BASE_DIR, 'buylist', 'range_level_results.json')

app = Flask(__name__)
app.secret_key = SECRET_KEY
app.config['MAX_CONTENT_LENGTH'] = 16 * 1024 * 1024  # 16MB max upload


def is_admin():
    return session.get('admin') is True

# Init tables on startup
try:
    init_tables()
    init_ideas_tables()
    init_ask_tables()
    init_asx_tables()
    init_dividend_tables()
    init_options_tables()
    init_tracker_tables()
    init_options_data_tables()
except Exception:
    pass


def fmt_num(val):
    """Format number removing unnecessary trailing zeros."""
    if val == int(val):
        return f"{int(val):,}"
    s = f"{val:,.4f}".rstrip('0')
    return s if not s.endswith('.') else s + '0'


def current_user_id():
    return session.get('user_id')

def current_username():
    return session.get('username', '')

LOG_FILE = os.path.join(BASE_DIR, 'last_run.log')
_job_lock   = threading.Lock()
_job_running = False
_job_name    = ''
_job_auto    = False   # True if the current job was auto-triggered (vs. an admin button click)


# ─── Sector performance helper ────────────────────────────────────────────────

SECTOR_ETFS = [
    ('XLK',  'Technology'),
    ('XLF',  'Financials'),
    ('XLE',  'Energy'),
    ('XLV',  'Healthcare'),
    ('XLI',  'Industrials'),
    ('XLY',  'Cons. Discretionary'),
    ('XLC',  'Communications'),
    ('XLP',  'Cons. Staples'),
    ('XLRE', 'Real Estate'),
    ('XLU',  'Utilities'),
    ('XLB',  'Materials'),
]

INDEX_ETFS = [
    ('SPY',  'S&P 500'),
    ('QQQ',  'Nasdaq 100'),
    ('DIA',  'Dow Jones'),
    ('IWM',  'Russell 2000'),
    ('SMH',  'Semiconductors'),
    ('XBI',  'Biotech'),
    ('GDX',  'Gold Miners'),
]

MACRO_INSTRUMENTS = [
    ('DX-Y.NYB', 'US Dollar (DXY)'),
    ('GC=F',     'Gold'),
    ('SI=F',     'Silver'),
    ('HG=F',     'Copper'),
    ('CL=F',     'Crude Oil'),
    ('^TNX',     'US 10Y Yield'),
]

DOW_30 = [
    'AAPL','AMGN','AMZN','AXP','BA','CAT','CRM','CSCO','CVX','DIS',
    'DOW','GS','HD','HON','IBM','JNJ','JPM','KO','MCD','MMM',
    'MRK','MSFT','NKE','NVDA','PG','TRV','UNH','V','VZ','WMT',
]

NASDAQ_100 = [
    'AAPL','MSFT','NVDA','AMZN','META','GOOGL','GOOG','TSLA','AVGO','COST',
    'NFLX','AMD','ADBE','QCOM','TMUS','TXN','AMGN','INTU','INTC','HON',
    'AMAT','CMCSA','BKNG','ISRG','MU','LRCX','PANW','ADI','KLAC','REGN',
    'CRWD','SNPS','CDNS','MELI','ORLY','ABNB','PYPL','CTAS','FTNT','NXPI',
    'MNST','MDLZ','ADP','PAYX','ROST','PCAR','MAR','CPRT','CHTR','MCHP',
    'WDAY','EXC','MRNA','KDP','DLTR','FAST','ODFL','EA','DXCM','CTSH',
    'XEL','BIIB','IDXX','TEAM','ZS','VRTX','ANSS','TTWO','ILMN','GEHC',
    'CEG','FANG','ON','CSGP','ENPH','WBD','LULU','MRVL','DASH','CSX',
    'VRSK','SBUX','ASML','PDD','SIRI','ALGN','SWKS','NTES','SMCI','ARM',
]

SP500_TICKERS = [
    'AAPL','MSFT','NVDA','AMZN','META','GOOGL','GOOG','TSLA','BRK-B','AVGO',
    'LLY','JPM','UNH','XOM','V','JNJ','MA','PG','HD','COST',
    'MRK','ABBV','CVX','WMT','BAC','KO','MCD','PEP','CSCO','ORCL',
    'ACN','TMO','CRM','WFC','LIN','ABT','AMD','NFLX','DIS','QCOM',
    'TXN','DHR','NKE','PM','INTC','HON','NEE','T','AMGN','UPS',
    'IBM','CAT','SBUX','RTX','GE','SPGI','BMY','LOW','INTU','GS',
    'DE','ELV','AMAT','MS','MMC','MDLZ','GILD','ADP','BKNG','SYK',
    'BLK','CVS','CB','ADI','LRCX','AMT','ISRG','TJX','VRTX','C',
    'REGN','SO','MO','ZTS','PLD','AXP','BSX','MMM','CL','SCHW',
    'DUK','MU','CI','BDX','HCA','EOG','KLAC','PNC','USB','ITW',
    'F','GM','ETN','CME','AON','PSA','FDX','TGT','SHW','NSC',
    'MCO','ECL','MAR','PANW','SNPS','CDNS','CRWD','ORLY','MELI','BA',
    'DELL','HPQ','HPE','PYPL','UBER','COIN','RIVN','SNAP','PINS','RBLX',
    'PLTR','ANET','SMCI','ARM','AXON','DDOG','HUBS','ZM','DOCU','OKTA',
    'SNOW','MDB','CFLT','GTLB','PATH','U','APPN','APPF','PCVX','TMDX',
    'WRB','AFL','MET','PRU','TRV','ALL','AIG','PFG','UNM','CNO',
    'DFS','COF','SYF','ADS','SLM','NAVI','CACC','OMF','ALLY','SOFI',
    'WFC','KEY','RF','FITB','CFG','HBAN','ZION','MTB','CMA','SIVB',
    'WAL','BOKF','WTFC','IBCP','FULT','SNV','GBCI','FBIZ','FFIN','TBBK',
]

def get_perf_data(tickers):
    """
    Returns {ticker: {d1, w1, m1, m3}} % change for each ticker.
    Pulls last 95 days of closes in one query.
    Also returns _error key if something went wrong, and _rows_found count.
    """
    from collections import defaultdict
    result = {t: {'d1': None, 'w1': None, 'm1': None, 'm3': None} for t in tickers}
    result['_error'] = None
    result['_rows_found'] = 0
    try:
        conn = get_connection()
        fmt = ','.join(['%s'] * len(tickers))
        with conn.cursor() as cur:
            cur.execute(f"""
                SELECT ticker, date, close
                FROM prices
                WHERE ticker IN ({fmt})
                  AND date >= DATE_SUB(CURDATE(), INTERVAL 95 DAY)
                ORDER BY ticker, date ASC
            """, [t.upper() for t in tickers])
            rows = cur.fetchall()
        conn.close()

        result['_rows_found'] = len(rows)

        grouped = defaultdict(list)
        for ticker, _, close in rows:
            if close is not None:
                grouped[ticker.upper()].append(float(close))

        def pct(closes, n):
            if len(closes) > n:
                return (closes[-1] - closes[-1 - n]) / closes[-1 - n] * 100
            return None

        for ticker in tickers:
            closes = grouped.get(ticker.upper(), [])
            if len(closes) >= 2:
                result[ticker]['d1'] = pct(closes, 1)
            if len(closes) >= 6:
                result[ticker]['w1'] = pct(closes, 5)
            if len(closes) >= 22:
                result[ticker]['m1'] = pct(closes, 21)
            if len(closes) >= 64:
                result[ticker]['m3'] = pct(closes, 63)
    except Exception as e:
        result['_error'] = str(e)
    return result


def get_us_sparklines_batch(tickers, bars=60):
    """Return {ticker: [last N closes]} from the prices table."""
    from collections import defaultdict
    result = defaultdict(list)
    if not tickers:
        return result
    try:
        conn = get_connection()
        fmt = ','.join(['%s'] * len(tickers))
        with conn.cursor() as cur:
            cur.execute(f"""
                SELECT ticker, close FROM prices
                WHERE ticker IN ({fmt})
                  AND date >= DATE_SUB(CURDATE(), INTERVAL 95 DAY)
                ORDER BY ticker, date ASC
            """, [t.upper() for t in tickers])
            for ticker, close in cur.fetchall():
                if close is not None:
                    result[ticker.upper()].append(float(close))
        conn.close()
        return {t: v[-bars:] for t, v in result.items()}
    except Exception:
        return result


def get_us_latest_prices(tickers):
    """Return {ticker: latest_close} from the prices table."""
    result = {}
    if not tickers:
        return result
    try:
        conn = get_connection()
        fmt = ','.join(['%s'] * len(tickers))
        with conn.cursor() as cur:
            cur.execute(f"""
                SELECT p.ticker, p.close
                FROM prices p
                INNER JOIN (
                    SELECT ticker, MAX(date) AS max_date
                    FROM prices WHERE ticker IN ({fmt})
                    GROUP BY ticker
                ) m ON p.ticker = m.ticker AND p.date = m.max_date
            """, [t.upper() for t in tickers])
            for ticker, close in cur.fetchall():
                result[ticker.upper()] = float(close) if close else None
        conn.close()
    except Exception:
        pass
    return result


def get_us_tickers_with_data(tickers):
    """Return set of tickers from the given list that have data in prices table."""
    if not tickers:
        return set()
    try:
        conn = get_connection()
        fmt = ','.join(['%s'] * len(tickers))
        with conn.cursor() as cur:
            cur.execute(f"SELECT DISTINCT ticker FROM prices WHERE ticker IN ({fmt})",
                        [t.upper() for t in tickers])
            result = {r[0].upper() for r in cur.fetchall()}
        conn.close()
        return result
    except Exception:
        return set()


def get_us_all_tickers_with_data():
    """Return all distinct tickers in the prices table."""
    try:
        conn = get_connection()
        with conn.cursor() as cur:
            cur.execute("SELECT DISTINCT ticker FROM prices ORDER BY ticker")
            result = [r[0].upper() for r in cur.fetchall()]
        conn.close()
        return result
    except Exception:
        return []


def perf_color(val):
    """Return background color based on % change magnitude."""
    if val is None:
        return '#1a1d2e'
    if val >= 5:    return '#166534'
    if val >= 3:    return '#15803d'
    if val >= 1.5:  return '#16a34a'
    if val >= 0.5:  return '#22c55e44'
    if val >= 0:    return '#22c55e22'
    if val >= -0.5: return '#ef444422'
    if val >= -1.5: return '#ef444444'
    if val >= -3:   return '#dc2626'
    if val >= -5:   return '#b91c1c'
    return '#7f1d1d'


def perf_text_color(val):
    if val is None: return '#555'
    return '#fff' if abs(val) >= 1.5 else ('#86efac' if val >= 0 else '#fca5a5')


# ─── DB helpers ──────────────────────────────────────────────────────────────

def get_db_stats():
    try:
        conn = get_connection()
        with conn.cursor() as cur:
            cur.execute("SELECT COUNT(DISTINCT ticker) FROM prices")
            tickers = cur.fetchone()[0]
            cur.execute("SELECT COUNT(*) FROM prices")
            rows = cur.fetchone()[0]
            cur.execute("SELECT MAX(date) FROM prices")
            latest = cur.fetchone()[0]
            cur.execute("SELECT MIN(date) FROM prices")
            earliest = cur.fetchone()[0]
        conn.close()
        return {
            'tickers': tickers,
            'rows': f"{rows:,}",
            'latest': str(latest) if latest else 'N/A',
            'earliest': str(earliest) if earliest else 'N/A',
            'error': None,
        }
    except Exception as e:
        return {'tickers': 0, 'rows': 0, 'latest': 'N/A', 'earliest': 'N/A', 'error': str(e)}


def get_log():
    if os.path.exists(LOG_FILE):
        with open(LOG_FILE, 'r') as f:
            return f.read()
    return 'No log yet.'


# ─── Background job ───────────────────────────────────────────────────────────

def _run_script(script_path, label):
    """
    Run an external Python script as a subprocess, streaming stdout to LOG_FILE.

    Used for long-running jobs (daily update, initial download) that are separate
    .py files rather than in-process functions. Clears _job_running when done.
    """
    global _job_running, _job_name
    with open(LOG_FILE, 'w') as f:
        f.write(f"=== {label} ===\nStarted: {datetime.now()}\n\n")
    try:
        proc = subprocess.Popen(
            [PYTHON, '-u', script_path],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, cwd=BASE_DIR
        )
        with open(LOG_FILE, 'a') as f:
            for line in proc.stdout:
                f.write(line)
                f.flush()
        proc.wait()
        with open(LOG_FILE, 'a') as f:
            f.write(f"\nFinished: {datetime.now()}\nExit code: {proc.returncode}\n")
    except Exception as e:
        with open(LOG_FILE, 'a') as f:
            f.write(f"\nERROR: {e}\n")
    finally:
        with _job_lock:
            _job_running = False
            _job_name = ''


def _run_scan_job():
    global _job_running, _job_name
    with open(LOG_FILE, 'w') as f:
        f.write(f"=== Channel Finder Scan ===\nStarted: {datetime.now()}\n\n")

    def log_to_file(msg):
        with open(LOG_FILE, 'a') as f:
            f.write(msg)
            f.flush()

    try:
        run_scan(log_callback=log_to_file)
    except Exception as e:
        log_to_file(f"\nERROR: {e}\n")
    finally:
        with _job_lock:
            _job_running = False
            _job_name = ''


def start_script_job(script_path, label):
    """
    Launch a background script job if no job is already running.

    Uses a threading.Lock so two admin button clicks can't start two jobs.
    Returns False (and does nothing) if a job is already in progress.
    PythonAnywhere's free tier is single-threaded in the web worker, but the
    daemon thread still runs — the lock prevents double-starts, not parallelism.
    """
    global _job_running, _job_name
    with _job_lock:
        if _job_running:
            return False
        _job_running = True
        _job_name = label
    t = threading.Thread(target=_run_script, args=(script_path, label), daemon=True)
    t.start()
    return True


def start_scan_job():
    global _job_running, _job_name
    with _job_lock:
        if _job_running:
            return False
        _job_running = True
        _job_name = 'Channel Scan'
    t = threading.Thread(target=_run_scan_job, daemon=True)
    t.start()
    return True


def _run_range_scan_job():
    global _job_running, _job_name
    with open(LOG_FILE, 'w') as f:
        f.write(f"=== Range Level Scan ===\nStarted: {datetime.now()}\n\n")
    try:
        from RangeLevelScanner import get_range_info, count_ranges_from_pivot, calculate_fader
        from EFI_Indicator import EFI_Indicator

        conn = get_connection()
        tickers = []
        with conn.cursor() as cur:
            cur.execute("SELECT DISTINCT ticker FROM prices ORDER BY ticker")
            tickers = [r[0] for r in cur.fetchall()]
        conn.close()

        with open(LOG_FILE, 'a') as f:
            f.write(f"Scanning {len(tickers)} tickers from DB...\n\n")

        setups = []
        for i, ticker in enumerate(tickers):
            try:
                conn = get_connection()
                df_raw = get_ticker_data(conn, ticker)
                conn.close()

                if df_raw is None or len(df_raw) < 70:
                    continue

                # Normalise column names to match scanner expectations
                df = df_raw.rename(columns={
                    'open': 'Open', 'high': 'High', 'low': 'Low',
                    'close': 'Close', 'volume': 'Volume'
                })
                df.index.name = 'Date'

                current_idx = len(df) - 1
                current_price = float(df['Close'].iloc[current_idx])

                if current_price < 0.50:
                    continue

                range_info = get_range_info(current_price)
                if range_info is None or range_info['zone'] not in ('NEAR_25', 'NEAR_75'):
                    continue

                indicator = EFI_Indicator()
                efi = indicator.calculate(df)
                current_fi_color   = efi['fi_color'].iloc[current_idx]
                current_force      = efi['force_index'].iloc[current_idx]
                current_norm_price = efi['normalized_price'].iloc[current_idx]

                fader_color = calculate_fader(df, current_idx)

                pivot_low, pivot_date, ranges_traveled = count_ranges_from_pivot(df, current_idx, lookback=60)
                if ranges_traveled >= 3:
                    continue

                if range_info['zone'] == 'NEAR_25':
                    trade_type   = 'WITHIN_RANGE'
                    entry_level  = range_info['levels']['L25']
                    stop_level   = range_info['levels']['L0']
                    target_level = range_info['levels']['L75']
                else:
                    trade_type   = 'RANGE_CHANGE'
                    entry_level  = range_info['levels']['L75']
                    stop_level   = range_info['levels']['L50']
                    next_low     = range_info['range_high']
                    target_level = next_low + range_info['range_size'] * 0.25

                risk   = entry_level - stop_level
                reward = target_level - entry_level
                rr_ratio = reward / risk if risk > 0 else 0

                quality_score = 0
                signal_notes  = []

                if fader_color == 'green':
                    quality_score += 25
                    signal_notes.append('Fader GREEN')
                if current_fi_color in ('lime', 'green'):
                    quality_score += 25
                    signal_notes.append('EFI bullish')
                elif current_fi_color == 'orange' and current_force > efi['force_index'].iloc[current_idx - 1]:
                    quality_score += 15
                    signal_notes.append('EFI improving')

                level_target = range_info['levels']['L25'] if trade_type == 'WITHIN_RANGE' else range_info['levels']['L75']
                dist_pct = abs(current_price - level_target) / range_info['range_size'] * 100
                if dist_pct < 5:
                    quality_score += 20
                    signal_notes.append('Tight to level')
                elif dist_pct < 10:
                    quality_score += 10

                if rr_ratio >= 2:
                    quality_score += 15
                    signal_notes.append(f"R:R {rr_ratio:.1f}")
                elif rr_ratio >= 1.5:
                    quality_score += 10

                if ranges_traveled < 1:
                    quality_score += 15
                    signal_notes.append('Fresh move')
                elif ranges_traveled < 2:
                    quality_score += 10

                if quality_score < 30:
                    continue

                setups.append({
                    'ticker': ticker,
                    'date': df.index[-1].strftime('%m/%d/%Y'),
                    'price': current_price,
                    'trade_type': trade_type,
                    'range_low': range_info['range_low'],
                    'range_high': range_info['range_high'],
                    'range_size': range_info['range_size'],
                    'position_pct': range_info['position_pct'],
                    'zone': range_info['zone'],
                    'L0': range_info['levels']['L0'],
                    'L25': range_info['levels']['L25'],
                    'L50': range_info['levels']['L50'],
                    'L75': range_info['levels']['L75'],
                    'L100': range_info['levels']['L100'],
                    'entry_level': entry_level,
                    'stop_level': stop_level,
                    'target_level': target_level,
                    'risk': risk,
                    'reward': reward,
                    'rr_ratio': rr_ratio,
                    'fader_color': fader_color,
                    'efi_color': current_fi_color,
                    'quality_score': quality_score,
                    'signal_notes': signal_notes,
                    'sparkline': df['Close'].tolist()[-40:],
                })

            except Exception:
                continue

            if (i + 1) % 100 == 0:
                with open(LOG_FILE, 'a') as f:
                    f.write(f"  {i+1}/{len(tickers)} scanned, {len(setups)} found so far\n")

        setups.sort(key=lambda x: x['price'])
        os.makedirs(os.path.dirname(RANGE_RESULTS_FILE), exist_ok=True)
        with open(RANGE_RESULTS_FILE, 'w') as f:
            json.dump({'scan_date': datetime.now().strftime('%Y-%m-%d %H:%M'),
                       'results': setups}, f)
        with open(LOG_FILE, 'a') as f:
            f.write(f"\nDone! Found {len(setups)} setups.\nFinished: {datetime.now()}\n")
    except Exception as e:
        import traceback
        with open(LOG_FILE, 'a') as f:
            f.write(f"\nERROR: {e}\n{traceback.format_exc()}\n")
    finally:
        with _job_lock:
            _job_running = False
            _job_name = ''


def start_range_scan_job():
    global _job_running, _job_name
    with _job_lock:
        if _job_running:
            return False
        _job_running = True
        _job_name = 'Range Scan'
    t = threading.Thread(target=_run_range_scan_job, daemon=True)
    t.start()
    return True


def _run_asx_download_job():
    global _job_running, _job_name
    with open(LOG_FILE, 'w') as f:
        f.write(f"=== ASX Data Download ===\nStarted: {datetime.now()}\n\n")
    try:
        import yfinance as yf
        import traceback as tb
        conn = get_connection()
        ok = 0
        errors = 0
        for i, ticker in enumerate(ASX_200):
            try:
                yf_ticker = ticker + '.AX'
                hist = yf.Ticker(yf_ticker).history(period='2y', interval='1d', auto_adjust=True)
                if hist is None or hist.empty:
                    continue
                # Flatten MultiIndex columns if present
                if isinstance(hist.columns, pd.MultiIndex):
                    hist.columns = [c[0] for c in hist.columns]
                rows = []
                for date, row in hist.iterrows():
                    try:
                        o = float(row['Open'])
                        h = float(row['High'])
                        l = float(row['Low'])
                        c = float(row['Close'])
                        v = int(row['Volume']) if pd.notna(row['Volume']) else 0
                        rows.append((ticker, date.strftime('%Y-%m-%d'), o, h, l, c, v))
                    except Exception:
                        continue
                if not rows:
                    continue
                with conn.cursor() as cur:
                    cur.executemany("""
                        INSERT INTO asx_prices (ticker, date, open, high, low, close, volume)
                        VALUES (%s, %s, %s, %s, %s, %s, %s)
                        ON DUPLICATE KEY UPDATE
                            open=VALUES(open), high=VALUES(high), low=VALUES(low),
                            close=VALUES(close), volume=VALUES(volume)
                    """, rows)
                conn.commit()
                ok += 1
            except Exception as e:
                errors += 1
                if errors <= 3:
                    with open(LOG_FILE, 'a') as f:
                        f.write(f"  ERROR {ticker}: {e}\n")
                continue

            if (i + 1) % 20 == 0:
                with open(LOG_FILE, 'a') as f:
                    f.write(f"  {i+1}/{len(ASX_200)} done — {ok} saved, {errors} errors\n")

        conn.close()
        with open(LOG_FILE, 'a') as f:
            f.write(f"\nDone! {ok}/{len(ASX_200)} tickers saved.\nFinished: {datetime.now()}\n")
    except Exception as e:
        import traceback
        with open(LOG_FILE, 'a') as f:
            f.write(f"\nFATAL ERROR: {e}\n{traceback.format_exc()}\n")
    finally:
        with _job_lock:
            _job_running = False
            _job_name = ''


def start_asx_download_job():
    global _job_running, _job_name
    with _job_lock:
        if _job_running:
            return False
        _job_running = True
        _job_name = 'ASX Download'
    t = threading.Thread(target=_run_asx_download_job, daemon=True)
    t.start()
    return True


def load_range_results():
    if not os.path.exists(RANGE_RESULTS_FILE):
        return None
    try:
        with open(RANGE_RESULTS_FILE) as f:
            return json.load(f)
    except Exception:
        return None


def sparkline_svg(closes, width=120, height=36):
    """Render a tiny inline SVG line chart from a list of close prices."""
    if len(closes) < 2:
        return f'<svg width="{width}" height="{height}"></svg>'
    mn, mx = min(closes), max(closes)
    if mn == mx:
        return f'<svg width="{width}" height="{height}"></svg>'
    pad = 2
    pts = []
    n = len(closes)
    for i, c in enumerate(closes):
        x = pad + i / (n - 1) * (width - pad * 2)
        y = pad + (1 - (c - mn) / (mx - mn)) * (height - pad * 2)
        pts.append(f"{x:.1f},{y:.1f}")
    color = '#22c55e' if closes[-1] >= closes[0] else '#ef4444'
    return (f'<svg width="{width}" height="{height}" style="display:block;vertical-align:middle">'
            f'<polyline points="{" ".join(pts)}" fill="none" stroke="{color}" stroke-width="1.5" stroke-linejoin="round"/>'
            f'</svg>')


# ─── Shared CSS + nav ─────────────────────────────────────────────────────────

BASE_CSS = """
* { box-sizing: border-box; margin: 0; padding: 0; }
body { font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
       background: #0f1117; color: #e0e0e0; min-height: 100vh; }
a { color: #60a5fa; text-decoration: none; }
a:hover { text-decoration: underline; }
header { background: #1a1d2e; border-bottom: 1px solid #2a2d3e;
         padding: 14px 28px; display: flex; align-items: center; gap: 20px; flex-wrap: wrap; }
header h1 { font-size: 1.1rem; font-weight: 700; color: #fff; }
nav { display: flex; gap: 6px; flex-wrap: wrap; }
nav a { padding: 6px 14px; border-radius: 6px; font-size: 0.82rem; font-weight: 500;
        color: #aaa; background: #252839; transition: background .15s ease, color .15s ease; }
nav a:hover, nav a.active { background: #3b82f6; color: #fff; text-decoration: none; }
.nav-dropdown { position: relative; }
.nav-dropdown-menu { display: flex; position: absolute; top: calc(100% + 6px); left: 0;
                      background: #1a1d2e; border: 1px solid #2a2d3e; border-radius: 8px;
                      padding: 6px; min-width: 180px; flex-direction: column; gap: 2px;
                      box-shadow: 0 8px 24px rgba(0,0,0,.4); z-index: 100;
                      opacity: 0; transform: translateY(-4px); pointer-events: none;
                      transition: opacity .15s ease, transform .15s ease; }
.nav-dropdown-menu.open { opacity: 1; transform: translateY(0); pointer-events: auto; }
.nav-dropdown-menu a { white-space: nowrap; }
.badge { font-size: 0.72rem; padding: 3px 10px; border-radius: 20px;
         font-weight: 600; color: #fff; margin-left: auto; transition: background .2s ease; }
#scan-progress-bar { position: relative; height: 3px; width: 100%; overflow: hidden;
                      background: #1a1d2e; }
#scan-progress-bar::after { content: ''; position: absolute; top: 0; left: -40%;
                            height: 100%; width: 40%;
                            background: linear-gradient(90deg, transparent, #3b82f6, #22c55e, transparent);
                            animation: scanbar 1.2s linear infinite; }
@keyframes scanbar { 0% { left: -40%; } 100% { left: 100%; } }
#scan-corner-alert { position: fixed; top: 16px; right: 16px; z-index: 9999;
                      background: #78350f; border: 1px solid #f59e0b; color: #fde68a;
                      padding: 12px 20px; border-radius: 10px; font-size: 0.95rem; font-weight: 700;
                      box-shadow: 0 8px 28px rgba(0,0,0,.5); display: none;
                      align-items: center; gap: 10px; animation: cornerPulse 1.6s ease-in-out infinite; }
#scan-corner-alert .dot { width: 10px; height: 10px; border-radius: 50%; background: #f59e0b;
                           animation: pulse 1.2s ease-in-out infinite; flex-shrink: 0; }
@keyframes cornerPulse { 0%,100% { box-shadow: 0 8px 28px rgba(245,158,11,.15); }
                         50%     { box-shadow: 0 8px 28px rgba(245,158,11,.55); } }
@keyframes pulse { 0%,100% { opacity: .4; } 50% { opacity: 1; } }
@media (max-width: 640px) {
  #scan-corner-alert { top: auto; bottom: 16px; right: 16px; left: 16px; font-size: 0.85rem; }
}
main { padding: 28px; max-width: 1200px; margin: 0 auto; animation: fadeIn .18s ease; }
@keyframes fadeIn { from { opacity: 0; } to { opacity: 1; } }
.card { background: #1a1d2e; border: 1px solid #2a2d3e; border-radius: 8px; padding: 20px; }
.grid4 { display: grid; grid-template-columns: repeat(auto-fit, minmax(180px,1fr)); gap: 14px; margin-bottom: 24px; }
.stat-label { font-size: 0.72rem; color: #666; text-transform: uppercase; letter-spacing:.05em; margin-bottom: 5px; }
.stat-value { font-size: 1.7rem; font-weight: 700; color: #fff; }
.stat-sub   { font-size: 0.78rem; color: #555; margin-top: 3px; }
section { background: #1a1d2e; border: 1px solid #2a2d3e; border-radius: 8px;
          padding: 22px; margin-bottom: 20px; }
h2 { font-size: 0.82rem; font-weight: 600; color: #777; text-transform: uppercase;
     letter-spacing:.06em; margin-bottom: 16px; }
.btn { display: inline-block; padding: 9px 18px; border-radius: 6px; font-size: 0.88rem;
       font-weight: 600; cursor: pointer; border: none; text-decoration: none; transition: opacity .15s; }
.btn:hover { opacity: .82; text-decoration: none; }
.btn-blue   { background: #3b82f6; color: #fff; }
.btn-amber  { background: #f59e0b; color: #000; }
.btn-green  { background: #22c55e; color: #000; }
.btn-off    { background: #252839; color: #555; cursor: not-allowed; }
.btn-row    { display: flex; gap: 10px; flex-wrap: wrap; align-items: center; }
.note       { font-size: 0.78rem; color: #555; margin-top: 10px; }
pre { background: #0a0c14; border: 1px solid #2a2d3e; border-radius: 6px; padding: 14px;
      font-size: 0.78rem; line-height: 1.5; max-height: 460px; overflow-y: auto;
      white-space: pre-wrap; word-break: break-word; color: #86efac; font-family: monospace; }
.err-box { background: #2a1515; border: 1px solid #ef4444; border-radius: 8px;
           padding: 14px; margin-bottom: 20px; color: #f87171; font-size:.85rem; }
"""

def nav_html(active=''):
    with _job_lock:
        running = _job_running
        jname = _job_name
    badge = f'<span id="job-badge" class="badge" style="background:#f59e0b">⚙ {jname}</span>' if running else \
            '<span id="job-badge" class="badge" style="background:#22c55e">● Idle</span>'
    progress_bar_style = 'display:block' if running else 'display:none'
    def lnk(href, label, key):
        cls = 'active' if active == key else ''
        return f'<a href="{href}" class="{cls}">{label}</a>'
    if is_admin():
        auth_btn = '<a href="/logout" style="font-size:.78rem;color:#555;margin-left:8px">Admin Logout</a>'
    elif current_user_id():
        auth_btn = f'<span style="font-size:.78rem;color:#aaa;margin-left:8px">Hi, {current_username()}</span> <a href="/ask/logout" style="font-size:.78rem;color:#555;margin-left:6px">Logout</a>'
    else:
        auth_btn = '<a href="/ask/login" style="font-size:.78rem;padding:5px 12px;background:#252839;border-radius:6px;color:#aaa">Login</a>'
    admin_lnk = f'<span style="width:1px;background:#2a2d3e;align-self:stretch;margin:0 4px"></span>{lnk("/admin","Admin","admin")}' if is_admin() else ''

    markets_keys = ('indexes', 'nasdaq', 'dow', 'sp500', 'russell', 'semiconductors')
    markets_active = 'active' if active in markets_keys else ''
    markets_menu = (
        lnk('/indexes', 'Indexes & ETFs', 'indexes') +
        lnk('/nasdaq', 'Nasdaq 100', 'nasdaq') +
        lnk('/dow', 'Dow 30', 'dow') +
        lnk('/sp500', 'S&amp;P 500', 'sp500') +
        lnk('/russell', 'Russell / Small Caps', 'russell') +
        lnk('/semiconductors', 'Semiconductors', 'semiconductors')
    )

    return f"""
    <header>
      <h1>Stock Manager</h1>
      <nav>
        {lnk('/','Dashboard','home')}
        {lnk('/signals','Signals','signals')}
        {lnk('/how-it-works','How It Works','howitworks')}
        <div class="nav-dropdown">
          <a href="javascript:void(0)" class="{markets_active}" onclick="toggleNavDropdown(event, this)">Markets ▾</a>
          <div class="nav-dropdown-menu">{markets_menu}</div>
        </div>
        {lnk('/picks',"Jimmy's Picks",'picks')}
        {lnk('/ideas',"Jimmy's Ideas",'ideas')}
        {lnk('/app','📱 App','mobileapp')}
        {lnk('/options-picks','Options Picks','optionspicks')}
        {lnk('/options-tracker','Options Tracker','optionstracker')}
        {lnk('/asx','ASX 200','asx')}
        {lnk('/asx/picks','ASX Picks','asxpicks')}
        {lnk('/dividend','Dividend Picks','dividend')}
        {lnk('/journal','Trade Journal','journal')}
        {lnk("/jangs-wicks","Jang's Wicks",'jangs-wicks')}
        {lnk('/ask','Ask Jimmy','ask')}
        {lnk('/kids','Kids Corner','kids')}
        {admin_lnk}
      </nav>
      {badge}
      {auth_btn}
    </header>
    <div id="scan-progress-bar" style="{progress_bar_style}"></div>
    <div id="scan-corner-alert" style="{'display:flex' if running else 'display:none'}">
      <span class="dot"></span><span id="scan-corner-text">⚙ {jname} running…</span>
    </div>
    <script>
    function toggleNavDropdown(e, btn) {{
      e.stopPropagation();
      const menu = btn.nextElementSibling;
      const isOpen = menu.classList.contains('open');
      document.querySelectorAll('.nav-dropdown-menu.open').forEach(m => m.classList.remove('open'));
      if (!isOpen) menu.classList.add('open');
    }}
    document.addEventListener('click', () => {{
      document.querySelectorAll('.nav-dropdown-menu.open').forEach(m => m.classList.remove('open'));
    }});
    (function() {{
      // A single "not running" read can be a fluke (slow response, dropped
      // request, momentary hiccup on a busy scan thread) — require 2 in a
      // row before we ever flip the display to idle, so a real still-running
      // scan can't get flashed as finished from one bad poll.
      var notRunningStreak = 0;
      function applyStatus(s) {{
        var badge = document.getElementById('job-badge');
        var bar = document.getElementById('scan-progress-bar');
        var corner = document.getElementById('scan-corner-alert');
        var cornerText = document.getElementById('scan-corner-text');
        if (!badge) return;
        if (s.running) {{
          notRunningStreak = 0;
          badge.textContent = '⚙ ' + s.job;
          badge.style.background = '#f59e0b';
          if (bar) bar.style.display = 'block';
          if (corner) corner.style.display = 'flex';
          if (cornerText) cornerText.textContent = '⚙ ' + s.job + ' running…';
        }} else {{
          notRunningStreak++;
          if (notRunningStreak < 2) return;
          badge.textContent = '● Idle';
          badge.style.background = '#22c55e';
          if (bar) bar.style.display = 'none';
          if (corner) corner.style.display = 'none';
        }}
      }}
      setInterval(function() {{
        fetch('/status').then(function(r) {{ return r.json(); }}).then(applyStatus).catch(function() {{}});
      }}, 5000);
    }})();
    </script>"""


def page_wrap(title, active, content, auto_refresh=False):
    """
    Return a complete HTML page string.

    Every route builds an HTML string for `content` and passes it here.
    We do not use Jinja templates for main pages — keeping everything in one
    Python file makes PythonAnywhere deployment a single file upload.

    active: nav link key (e.g. 'picks', 'admin', 'results') — highlighted in nav.
    auto_refresh: set True on log/status pages that should poll while a job runs.
    """
    poll_script = ''
    if auto_refresh:
        # Poll /status instead of a hard <meta refresh> reload — only swap the
        # page in once, in place, the moment the job finishes (no repeated
        # full-page flashes/scroll resets while it's still running).
        poll_script = """
    <script>
    (function() {
      var notRunningStreak = 0;
      var iv = setInterval(function() {
        fetch('/status').then(function(r) { return r.json(); }).then(function(s) {
          if (s.running) { notRunningStreak = 0; return; }
          notRunningStreak++;
          if (notRunningStreak < 2) return;
          clearInterval(iv);
          fetch(location.href).then(function(r) { return r.text(); }).then(function(html) {
            var doc = new DOMParser().parseFromString(html, 'text/html');
            var newMain = doc.querySelector('main');
            var curMain = document.querySelector('main');
            if (newMain && curMain) {
              curMain.innerHTML = newMain.innerHTML;
              curMain.querySelectorAll('script').forEach(function(oldScript) {
                var newScript = document.createElement('script');
                for (var i = 0; i < oldScript.attributes.length; i++) {
                  var a = oldScript.attributes[i];
                  newScript.setAttribute(a.name, a.value);
                }
                newScript.textContent = oldScript.textContent;
                oldScript.parentNode.replaceChild(newScript, oldScript);
              });
            }
            document.title = doc.title;
          });
        }).catch(function() {});
      }, 2000);
    })();
    </script>"""
    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>{title} — Stock Manager</title>
<style>{BASE_CSS}</style>
</head>
<body>
{nav_html(active)}
<main>{content}</main>
{poll_script}
</body>
</html>"""


# ─── Dashboard ────────────────────────────────────────────────────────────────

@app.route('/')
def index():
    stats     = get_db_stats()

    # ── US portfolio ──────────────────────────────────────────────────────────
    positions    = get_positions()
    history      = get_history()
    cash         = get_account()
    port_val     = get_portfolio_value(positions)
    total_val    = cash + port_val
    total_pnl    = total_val - 100_000.0
    closed       = [t for t in history if t['pnl'] is not None]
    wins         = [t for t in closed if t['pnl'] > 0]
    win_rate     = (len(wins) / len(closed) * 100) if closed else 0
    total_realised = sum(t['pnl'] for t in closed)

    # ── ASX portfolio ─────────────────────────────────────────────────────────
    asx_positions = get_asx_picks()
    asx_cash      = get_asx_account()
    asx_port_val  = get_asx_portfolio_value(asx_positions)
    asx_total_val = asx_cash + asx_port_val
    asx_total_pnl = asx_total_val - 100_000.0
    asx_open_pnl  = sum(p['pnl'] for p in asx_positions)

    with _job_lock:
        running = _job_running

    err = f'<div class="err-box"><strong>DB Error:</strong> {stats["error"]}</div>' if stats['error'] else ''

    def pnl_html(val):
        c = '#22c55e' if val >= 0 else '#ef4444'
        s = '+' if val >= 0 else ''
        return f'<span style="color:{c};font-weight:700">{s}${val:,.2f}</span>'

    def pnl_pct_html(val, basis=100_000):
        c = '#22c55e' if val >= 0 else '#ef4444'
        s = '+' if val >= 0 else ''
        return f'<span style="color:{c};font-size:.85rem">{s}{val/basis*100:.2f}%</span>'

    wr_color = '#22c55e' if win_rate >= 50 else '#ef4444'
    rp_color = '#22c55e' if total_realised >= 0 else '#ef4444'
    rp_sign  = '+' if total_realised >= 0 else ''

    # ── US open positions P&L rows ────────────────────────────────────────────
    def pos_rows(pos_list, link_prefix='/chart/'):
        rows = ''
        for p in sorted(pos_list, key=lambda x: x['pnl'], reverse=True):
            pc = '#22c55e' if p['pnl'] >= 0 else '#ef4444'
            ps = '+' if p['pnl'] >= 0 else ''
            rows += f"""<tr>
              <td><a href="{link_prefix}{p['ticker']}" style="color:#60a5fa;font-weight:700">{p['ticker']}</a></td>
              <td style="color:#aaa">{p.get('bought_date','')}</td>
              <td style="color:#fff">${p['current_price']:.2f}</td>
              <td style="color:#555">${p['buy_price']:.2f}</td>
              <td style="color:{pc};font-weight:600">{ps}${p['pnl']:,.2f}</td>
              <td style="color:{pc}">{ps}{p['pnl_pct']:.1f}%</td>
            </tr>"""
        return rows

    us_pos_rows  = pos_rows(positions)
    asx_pos_rows = pos_rows(asx_positions)

    pos_table_style = """
      <style>
        .pos-table{width:100%;border-collapse:collapse;font-size:.82rem}
        .pos-table th{text-align:left;padding:7px 10px;color:#555;border-bottom:1px solid #2a2d3e;font-weight:500}
        .pos-table td{padding:7px 10px;border-bottom:1px solid #151820}
        .pos-table tr:hover td{background:#1f2235}
      </style>"""

    us_table = (f'{pos_table_style}<table class="pos-table">'
                f'<tr><th>Ticker</th><th>Bought</th><th>Price</th><th>Cost</th><th>P&L $</th><th>P&L %</th></tr>'
                f'{us_pos_rows}</table>') if us_pos_rows else '<p class="note">No open positions.</p>'

    asx_table = (f'<table class="pos-table">'
                 f'<tr><th>Ticker</th><th>Bought</th><th>Price</th><th>Cost</th><th>P&L A$</th><th>P&L %</th></tr>'
                 f'{asx_pos_rows}</table>') if asx_pos_rows else '<p class="note">No open ASX positions.</p>'

    # ── Recent US trade history rows ──────────────────────────────────────────
    hist_rows = ''
    for t in history[:8]:
        action_color = '#22c55e' if t['action'] == 'BUY' else '#ef4444'
        pnl_str = ''
        if t['pnl'] is not None:
            pc = '#22c55e' if t['pnl'] >= 0 else '#ef4444'
            ps = '+' if t['pnl'] >= 0 else ''
            pnl_str = f'<span style="color:{pc}">{ps}${t["pnl"]:,.2f}</span>'
        hist_rows += f"""<tr>
          <td>{t['trade_date']}</td>
          <td><a href="/chart/{t['ticker']}" style="color:#60a5fa;font-weight:700">{t['ticker']}</a></td>
          <td><span style="color:{action_color};font-weight:700">{t['action']}</span></td>
          <td>${fmt_num(t['price'])}</td>
          <td>${t['total']:,.2f}</td>
          <td>{pnl_str}</td>
        </tr>"""

    content = f"""
    {err}
    <style>
      .port-hero {{
        border-radius:12px; padding:24px 28px; margin-bottom:12px;
        border:1px solid #2a2d3e;
      }}
      .port-hero .label {{ font-size:.72rem;color:#555;text-transform:uppercase;letter-spacing:.1em;margin-bottom:4px }}
      .port-hero .total {{ font-size:2.2rem;font-weight:800;color:#fff;margin-bottom:2px }}
      .port-hero .sub   {{ font-size:.88rem }}
      .port-hero .open-pnl {{ font-size:.82rem;color:#777;margin-top:6px }}
    </style>

    <!-- Side-by-side portfolio heroes -->
    <div style="display:grid;grid-template-columns:1fr 1fr;gap:14px;margin-bottom:24px">

      <!-- US Picks -->
      <div class="port-hero" style="background:linear-gradient(135deg,#1a1d2e 0%,#0f1117 100%)">
        <div class="label">🇺🇸 US Picks — $100k</div>
        <div class="total">${total_val:,.2f}</div>
        <div class="sub">{pnl_html(total_pnl)} &nbsp; {pnl_pct_html(total_pnl)}</div>
        <div class="open-pnl">
          {len(positions)} open &nbsp;·&nbsp;
          Cash ${cash:,.2f} &nbsp;·&nbsp;
          Realised <span style="color:{'#22c55e' if total_realised>=0 else '#ef4444'}">{rp_sign}${total_realised:,.2f}</span>
        </div>
        <div style="margin-top:10px">
          <a href="/picks" style="font-size:.78rem;color:#3b82f6">View picks →</a>
        </div>
      </div>

      <!-- ASX Picks -->
      <div class="port-hero" style="background:linear-gradient(135deg,#1a2420 0%,#0f1117 100%)">
        <div class="label">🇦🇺 ASX Picks — A$100k</div>
        <div class="total">A${asx_total_val:,.2f}</div>
        <div class="sub">{pnl_html(asx_total_pnl)} &nbsp; {pnl_pct_html(asx_total_pnl)}</div>
        <div class="open-pnl">
          {len(asx_positions)} open &nbsp;·&nbsp;
          Cash A${asx_cash:,.2f} &nbsp;·&nbsp;
          Unrealised {pnl_html(asx_open_pnl)}
        </div>
        <div style="margin-top:10px">
          <a href="/asx/picks" style="font-size:.78rem;color:#3b82f6">View picks →</a>
        </div>
      </div>

    </div>

    <!-- Stats row -->
    <div class="grid4" style="margin-bottom:24px">
      <div class="card">
        <div class="stat-label">US Cash</div>
        <div class="stat-value" style="font-size:1.4rem">${cash:,.2f}</div>
        <div class="stat-sub">{len(positions)} open positions</div>
      </div>
      <div class="card">
        <div class="stat-label">ASX Cash</div>
        <div class="stat-value" style="font-size:1.4rem">A${asx_cash:,.2f}</div>
        <div class="stat-sub">{len(asx_positions)} open positions</div>
      </div>
      <div class="card">
        <div class="stat-label">US Win Rate</div>
        <div class="stat-value" style="font-size:1.4rem;color:{wr_color}">{win_rate:.0f}%</div>
        <div class="stat-sub">{len(wins)} wins / {len(closed)} closed</div>
      </div>
      <div class="card">
        <div class="stat-label">US Realised P&amp;L</div>
        <div class="stat-value" style="font-size:1.4rem;color:{rp_color}">{rp_sign}${total_realised:,.2f}</div>
        <div class="stat-sub">from closed trades</div>
      </div>
    </div>

    <!-- Open positions side by side -->
    <div style="display:grid;grid-template-columns:1fr 1fr;gap:14px;margin-bottom:24px">
      <section style="margin:0">
        <h2>US Open Positions
          <a href="/picks" style="font-size:.75rem;font-weight:400;color:#3b82f6;text-transform:none;margin-left:8px;letter-spacing:0">manage →</a>
        </h2>
        {us_table}
      </section>
      <section style="margin:0">
        <h2>ASX Open Positions
          <a href="/asx/picks" style="font-size:.75rem;font-weight:400;color:#3b82f6;text-transform:none;margin-left:8px;letter-spacing:0">manage →</a>
        </h2>
        {asx_table}
      </section>
    </div>

    <!-- Recent US trades -->
    <section style="margin-bottom:24px">
      <h2>Recent US Trades <a href="/picks" style="font-size:.75rem;font-weight:400;color:#3b82f6;text-transform:none;margin-left:10px;letter-spacing:0">View all →</a></h2>
      <style>
        .trade-table{{width:100%;border-collapse:collapse;font-size:.83rem}}
        .trade-table th{{text-align:left;padding:8px 10px;color:#555;border-bottom:1px solid #2a2d3e;font-weight:500}}
        .trade-table td{{padding:8px 10px;border-bottom:1px solid #151820}}
        .trade-table tr:hover td{{background:#1f2235}}
      </style>
      {'<table class="trade-table"><tr><th>Date</th><th>Ticker</th><th>Action</th><th>Price</th><th>Total</th><th>P&L</th></tr>' + hist_rows + '</table>' if hist_rows else '<p class="note">No trades yet. <a href="/picks">Add your first pick →</a></p>'}
    </section>

    {f'<div style="text-align:right;margin-top:4px"><a href="/admin" style="font-size:.78rem;color:#555">→ Admin Panel</a></div>' if is_admin() else ''}
    """

    return page_wrap('Dashboard', 'home', content, auto_refresh=running)


# ─── Channel Scanner ──────────────────────────────────────────────────────────

@app.route('/scan')
def scan_page():
    with _job_lock:
        running = _job_running
        jname = _job_name

    last = load_last_results()
    last_info = ''
    if last:
        last_info = f'<p class="note">Last scan: {last["scan_date"]} — {last["total"]} setups found ({last["both"]} BOTH, {last["single"]} SINGLE). <a href="/results">View results →</a></p>'

    if not is_admin():
        btn = ''
    elif running and jname == 'Channel Scan':
        btn = '<span class="btn btn-off">Scan Running...</span>'
    elif running:
        btn = '<span class="btn btn-off">Another job running</span>'
    else:
        btn = '<a href="/run-scan" class="btn btn-green">▶ Run Channel Scanner</a>'

    log_section = ''
    if running and jname == 'Channel Scan':
        log_section = f'<section><h2>Live Log</h2><pre>{get_log().replace("<","&lt;")}</pre></section>'

    content = f"""
    <section>
      <h2>Channel Finder Scanner</h2>
      <p style="color:#aaa;margin-bottom:16px;font-size:.9rem">
        Scans all {{}}) tickers for EMA squeeze channels on Daily + Weekly timeframes.<br>
        <strong style="color:#fff">BOTH (2/2)</strong> = daily + weekly channel aligned.
        <strong style="color:#fff">SINGLE (1/2)</strong> = one timeframe only.
      </p>
      <div class="btn-row">{btn}</div>
      {last_info}
    </section>
    {log_section}"""

    return page_wrap('Channel Scanner', 'scan', content, auto_refresh=(running and jname == 'Channel Scan'))


@app.route('/run-scan')
def run_scan_route():
    if not is_admin():
        return redirect('/scan')
    start_scan_job()
    return redirect('/scan')


# ─── Results ─────────────────────────────────────────────────────────────────

@app.route('/results')
def results_page():
    data = load_last_results()

    if not data:
        content = '<section><h2>No Results Yet</h2><p class="note">Run the Channel Scanner first.</p><br><a href="/scan" class="btn btn-green">Go to Scanner</a></section>'
        return page_wrap('Results', 'results', content)

    results = data['results']
    both_rows   = [r for r in results if r['score'] == 2]
    single_rows = [r for r in results if r['score'] == 1]

    # Batch-fetch last 40 closes for all tickers in one query
    all_tickers = [r['ticker'] for r in results]
    sparklines = {}
    try:
        fmt = ','.join(['%s'] * len(all_tickers))
        conn = get_connection()
        with conn.cursor() as cur:
            cur.execute(f"""
                SELECT ticker, date, close
                FROM prices
                WHERE ticker IN ({fmt})
                ORDER BY ticker, date ASC
            """, all_tickers)
            for ticker, _, close in cur.fetchall():
                sparklines.setdefault(ticker, []).append(float(close))
        conn.close()
        # Keep only last 40
        sparklines = {t: v[-40:] for t, v in sparklines.items()}
    except Exception:
        pass

    def rows_html(items):
        html = ''
        for r in items:
            w = '✓' if r['weekly'] else '–'
            d = '✓' if r['daily']  else '–'
            score_color = '#22c55e' if r['score'] == 2 else '#f59e0b'
            svg = sparkline_svg(sparklines.get(r['ticker'], []))
            html += f"""
            <tr class="res-row" data-ticker="{r['ticker']}" style="cursor:pointer">
              <td>
                <div style="display:flex;align-items:center;gap:10px">
                  <strong style="color:#60a5fa;min-width:52px">{r['ticker']}</strong>
                  {svg}
                </div>
              </td>
              <td data-val="{r['price']}">${r['price']:,.4f}</td>
              <td data-val="{r['score']}"><span style="color:{score_color};font-weight:700">{r['score']}/2</span></td>
              <td style="color:{'#22c55e' if r['weekly'] else '#555'}">{w}</td>
              <td style="color:{'#22c55e' if r['daily'] else '#555'}">{d}</td>
            </tr>"""
        return html

    table_style = """
    <style>
    table { width:100%; border-collapse:collapse; font-size:.85rem; }
    th { text-align:left; padding:8px 12px; color:#555; border-bottom:1px solid #2a2d3e;
         font-weight:500; cursor:pointer; user-select:none; white-space:nowrap; }
    th:hover { color:#aaa; }
    th.sort-asc::after  { content:' ▲'; font-size:.65rem; color:#60a5fa; }
    th.sort-desc::after { content:' ▼'; font-size:.65rem; color:#60a5fa; }
    td { padding:9px 12px; border-bottom:1px solid #151820; }
    tr:hover td { background:#1f2235; }
    </style>
    <script>
    function sortTable(th) {
      const table = th.closest('table');
      const tbody = table.querySelector('tbody');
      const idx = th.cellIndex;
      const asc = th.classList.contains('sort-desc');
      table.querySelectorAll('th').forEach(h => h.classList.remove('sort-asc','sort-desc'));
      th.classList.add(asc ? 'sort-asc' : 'sort-desc');
      const rows = Array.from(tbody.querySelectorAll('tr'));
      rows.sort((a, b) => {
        const av = a.cells[idx].dataset.val ?? a.cells[idx].textContent.trim();
        const bv = b.cells[idx].dataset.val ?? b.cells[idx].textContent.trim();
        const an = parseFloat(av), bn = parseFloat(bv);
        const cmp = isNaN(an) ? av.localeCompare(bv) : an - bn;
        return asc ? cmp : -cmp;
      });
      rows.forEach(r => tbody.appendChild(r));
    }
    </script>"""

    chart_js = """
    <script src="https://unpkg.com/lightweight-charts@4.1.3/dist/lightweight-charts.standalone.production.js"></script>
    <script>
    document.querySelectorAll('.res-row').forEach(row => {
      row.addEventListener('click', () => {
        const ticker = row.dataset.ticker;
        const existId = 'rdrop-' + ticker;
        const exist = document.getElementById(existId);

        if (exist) {
          exist.remove();
          row.classList.remove('active');
          return;
        }

        document.querySelectorAll('.res-drop').forEach(d => d.remove());
        document.querySelectorAll('.res-row.active').forEach(r => r.classList.remove('active'));
        row.classList.add('active');

        const drop = document.createElement('tr');
        drop.id = existId;
        drop.className = 'res-drop';
        drop.innerHTML = `<td colspan="5" style="background:#080a10;padding:16px 20px">
          <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:10px">
            <span style="color:#fff;font-weight:700;font-size:1rem">${ticker}</span>
            <span style="color:#555;font-size:.75rem" id="rs-${ticker}">Loading...</span>
            <a href="/chart/${ticker}" style="font-size:.78rem;color:#60a5fa;margin-left:16px">Open full chart →</a>
          </div>
          <div id="rm-${ticker}" style="height:360px;background:#0a0c14;border-radius:6px"></div>
          <div id="rv-${ticker}" style="height:70px;background:#0a0c14;border-radius:6px;margin-top:3px"></div>
        </td>`;
        row.parentNode.insertBefore(drop, row.nextSibling);

        fetch('/api/chart-data/' + ticker)
          .then(r => r.json())
          .then(data => {
            if (data.error) { document.getElementById('rs-' + ticker).textContent = data.error; return; }
            document.getElementById('rs-' + ticker).textContent = data.bars + ' bars · ' + data.date_range;

            const chart = LightweightCharts.createChart(document.getElementById('rm-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: true },
              crosshair: { mode: LightweightCharts.CrosshairMode.Normal },
            });
            const candles = chart.addCandlestickSeries({
              upColor: '#22c55e', downColor: '#ef4444',
              borderUpColor: '#22c55e', borderDownColor: '#ef4444',
              wickUpColor: '#22c55e', wickDownColor: '#ef4444',
            });
            candles.setData(data.ohlcv);
            const ema5  = chart.addLineSeries({ color: '#60a5fa', lineWidth: 1, title: 'EMA5' });
            const ema26 = chart.addLineSeries({ color: '#f59e0b', lineWidth: 1, title: 'EMA26' });
            ema5.setData(data.ema5);
            ema26.setData(data.ema26);
            chart.timeScale().fitContent();

            const volChart = LightweightCharts.createChart(document.getElementById('rv-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: false },
            });
            const volS = volChart.addHistogramSeries({ priceFormat: { type: 'volume' }, priceScaleId: '' });
            volS.priceScale().applyOptions({ scaleMargins: { top: 0.1, bottom: 0 } });
            volS.setData(data.volume);
            volChart.timeScale().fitContent();

            chart.timeScale().subscribeVisibleLogicalRangeChange(r => volChart.timeScale().setVisibleLogicalRange(r));
            volChart.timeScale().subscribeVisibleLogicalRangeChange(r => chart.timeScale().setVisibleLogicalRange(r));
          })
          .catch(e => { document.getElementById('rs-' + ticker).textContent = 'Failed: ' + e; });
      });
    });
    </script>"""

    def make_section(title, items):
        if not items:
            return ''
        return f"""
        <section style="margin-bottom:20px">
          <h2>{title} <span style="color:#555;font-size:.75rem;font-weight:400;text-transform:none;letter-spacing:0">— click a row to expand chart</span></h2>
          {table_style}
          <table>
            <thead><tr>
              <th onclick="sortTable(this)">Ticker</th>
              <th onclick="sortTable(this)" class="sort-desc">Price</th>
              <th onclick="sortTable(this)">Score</th>
              <th>Weekly</th><th>Daily</th>
            </tr></thead>
            <tbody>{rows_html(items)}</tbody>
          </table>
        </section>"""

    summary = f"""
    <section style="padding:16px 22px;margin-bottom:20px">
      <div style="display:flex;gap:32px;align-items:center;flex-wrap:wrap">
        <div><span style="color:#555;font-size:.8rem">Scan date:</span>
             <strong style="margin-left:8px">{data['scan_date']}</strong></div>
        <div><span style="color:#555;font-size:.8rem">Total:</span>
             <strong style="margin-left:8px">{data['total']}</strong></div>
        <div><span style="color:#22c55e;font-size:.8rem">BOTH:</span>
             <strong style="margin-left:8px;color:#22c55e">{data['both']}</strong></div>
        <div><span style="color:#f59e0b;font-size:.8rem">SINGLE:</span>
             <strong style="margin-left:8px;color:#f59e0b">{data['single']}</strong></div>
        <a href="/run-scan" class="btn btn-green" style="margin-left:auto;padding:7px 16px;font-size:.82rem">Re-run Scan</a>
      </div>
    </section>"""

    content = summary + make_section(f'BOTH — Daily + Weekly Channel ({len(both_rows)} stocks)', both_rows) + \
              make_section(f'SINGLE — One Timeframe ({len(single_rows)} stocks)', single_rows) + chart_js
    return page_wrap('Results', 'results', content)


# ─── Chart ────────────────────────────────────────────────────────────────────

@app.route('/chart/<ticker>')
def chart_page(ticker):
    ticker = ticker.upper()
    content = f"""
    <div style="margin-bottom:16px;display:flex;align-items:center;gap:16px">
      <a href="/results" style="color:#555;font-size:.85rem">← Back to Results</a>
      <h1 style="font-size:1.4rem;font-weight:700;color:#fff">{ticker}</h1>
    </div>

    <section style="padding:16px">
      <div id="chart" style="width:100%;height:520px;background:#0a0c14;border-radius:6px"></div>
      <div id="volume-chart" style="width:100%;height:120px;background:#0a0c14;border-radius:6px;margin-top:4px"></div>
      <div id="status" style="color:#555;font-size:.8rem;margin-top:8px">Loading chart data...</div>
    </section>

    <section style="padding:16px">
      <div id="info-bar" style="display:flex;gap:28px;flex-wrap:wrap;font-size:.88rem"></div>
    </section>

    <section style="padding:16px">
      <div style="display:flex;align-items:center;gap:12px;margin-bottom:10px;flex-wrap:wrap">
        <button id="opt-lookup-btn" class="btn btn-blue" onclick="lookupOptionsChain()">Look Up Options Chain</button>
        <select id="opt-expiry-select" style="display:none;background:#0a0c14;border:1px solid #2a2d3e;
                border-radius:6px;color:#fff;padding:7px 10px;font-size:.85rem" onchange="lookupOptionsChain(this.value)"></select>
        <span id="opt-lookup-status" style="color:#555;font-size:.8rem"></span>
      </div>
      <div id="opt-lookup-panel"></div>
    </section>

    <script src="https://unpkg.com/lightweight-charts@4.1.3/dist/lightweight-charts.standalone.production.js"></script>
    <script>
    const ticker = "{ticker}";

    function lookupOptionsChain(expiry) {{
      const statusEl = document.getElementById('opt-lookup-status');
      const btn = document.getElementById('opt-lookup-btn');
      statusEl.textContent = 'Fetching real chain from the market…';
      btn.disabled = true;
      const url = '/api/options-lookup/' + ticker + (expiry ? ('?expiry=' + expiry) : '');
      fetch(url)
        .then(r => r.json())
        .then(data => {{
          btn.disabled = false;
          if (data.error) {{ statusEl.textContent = 'Error: ' + data.error; return; }}
          statusEl.textContent = 'Spot $' + data.spot.toFixed(2) + ' · expiry ' + data.expiry;

          const sel = document.getElementById('opt-expiry-select');
          sel.style.display = '';
          sel.innerHTML = data.available_expirations.map(e =>
            '<option value="' + e + '"' + (e === data.expiry ? ' selected' : '') + '>' + e + '</option>'
          ).join('');

          const rowHtml = (c, p) => {{
            const cell = (x, color) => x == null ? '<td style="color:#444">—</td>' :
              '<td style="color:' + color + '">' + x + '</td>';
            return '<tr>' +
              cell(c ? '$' + c.last_price?.toFixed(2) : null, '#22c55e') +
              cell(c ? '$' + c.bid?.toFixed(2) : null, '#666') +
              cell(c ? '$' + c.ask?.toFixed(2) : null, '#666') +
              cell(c && c.volume != null ? c.volume : null, '#666') +
              '<td style="font-weight:700">$' + (c ? c.strike : p.strike).toFixed(2) + '</td>' +
              cell(p && p.volume != null ? p.volume : null, '#666') +
              cell(p ? '$' + p.bid?.toFixed(2) : null, '#666') +
              cell(p ? '$' + p.ask?.toFixed(2) : null, '#666') +
              cell(p ? '$' + p.last_price?.toFixed(2) : null, '#ef4444') +
              '</tr>';
          }};

          const strikes = Array.from(new Set([...data.calls, ...data.puts].map(x => x.strike))).sort((a,b) => a-b);
          let rows = '';
          strikes.forEach(k => {{
            const c = data.calls.find(x => x.strike === k);
            const p = data.puts.find(x => x.strike === k);
            rows += rowHtml(c, p);
          }});

          document.getElementById('opt-lookup-panel').innerHTML = `
            <p class="note" style="margin-bottom:10px">Real market quotes (yfinance), cached for use elsewhere on the site.</p>
            <div style="overflow-x:auto">
            <table style="width:100%;border-collapse:collapse;font-size:.85rem;min-width:600px">
              <tr>
                <th colspan="4" style="background:#062e17;color:#4ade80;padding:6px 10px;text-align:center">Calls</th>
                <th></th>
                <th colspan="4" style="background:#3b0f2e;color:#f9a8d4;padding:6px 10px;text-align:center">Puts</th>
              </tr>
              <tr style="color:#555;font-size:.75rem">
                <th style="padding:6px 10px">Last</th><th>Bid</th><th>Ask</th><th>Vol</th>
                <th style="padding:6px 10px">Strike</th>
                <th>Vol</th><th>Bid</th><th>Ask</th><th style="padding:6px 10px">Last</th>
              </tr>
              ${{rows}}
            </table>
            </div>`;
        }})
        .catch(e => {{ btn.disabled = false; statusEl.textContent = 'Failed: ' + e; }});
    }}
    </script>
    <script>
    // keep the OHLCV/EMA loader below scoped separately

    fetch('/api/chart-data/' + ticker)
      .then(r => r.json())
      .then(data => {{
        if (data.error) {{
          document.getElementById('status').textContent = 'Error: ' + data.error;
          return;
        }}

        document.getElementById('status').textContent =
          data.bars + ' daily bars  |  ' + data.date_range;

        // Main price chart
        const chart = LightweightCharts.createChart(document.getElementById('chart'), {{
          layout: {{ background: {{ color: '#0a0c14' }}, textColor: '#888' }},
          grid: {{ vertLines: {{ color: '#1a1d2e' }}, horzLines: {{ color: '#1a1d2e' }} }},
          rightPriceScale: {{ borderColor: '#2a2d3e' }},
          timeScale: {{ borderColor: '#2a2d3e', timeVisible: true }},
          crosshair: {{ mode: LightweightCharts.CrosshairMode.Normal }},
        }});

        const candles = chart.addCandlestickSeries({{
          upColor: '#22c55e', downColor: '#ef4444',
          borderUpColor: '#22c55e', borderDownColor: '#ef4444',
          wickUpColor: '#22c55e', wickDownColor: '#ef4444',
        }});
        candles.setData(data.ohlcv);

        // EMA lines
        const ema5 = chart.addLineSeries({{ color: '#60a5fa', lineWidth: 1, title: 'EMA5' }});
        const ema26 = chart.addLineSeries({{ color: '#f59e0b', lineWidth: 1, title: 'EMA26' }});
        ema5.setData(data.ema5);
        ema26.setData(data.ema26);

        chart.timeScale().fitContent();

        // Volume chart
        const volChart = LightweightCharts.createChart(document.getElementById('volume-chart'), {{
          layout: {{ background: {{ color: '#0a0c14' }}, textColor: '#888' }},
          grid: {{ vertLines: {{ color: '#1a1d2e' }}, horzLines: {{ color: '#1a1d2e' }} }},
          rightPriceScale: {{ borderColor: '#2a2d3e' }},
          timeScale: {{ borderColor: '#2a2d3e', timeVisible: true }},
        }});

        const volSeries = volChart.addHistogramSeries({{
          priceFormat: {{ type: 'volume' }},
          priceScaleId: '',
        }});
        volSeries.priceScale().applyOptions({{ scaleMargins: {{ top: 0.1, bottom: 0 }} }});
        volSeries.setData(data.volume);
        volChart.timeScale().fitContent();

        // Sync time scales
        chart.timeScale().subscribeVisibleLogicalRangeChange(range => {{
          volChart.timeScale().setVisibleLogicalRange(range);
        }});
        volChart.timeScale().subscribeVisibleLogicalRangeChange(range => {{
          chart.timeScale().setVisibleLogicalRange(range);
        }});

        // Info bar
        const last = data.ohlcv[data.ohlcv.length - 1];
        const info = document.getElementById('info-bar');
        info.innerHTML = `
          <span><span style="color:#555">Open</span> <strong>${{last.open.toFixed(4)}}</strong></span>
          <span><span style="color:#555">High</span> <strong style="color:#22c55e">${{last.high.toFixed(4)}}</strong></span>
          <span><span style="color:#555">Low</span>  <strong style="color:#ef4444">${{last.low.toFixed(4)}}</strong></span>
          <span><span style="color:#555">Close</span><strong>${{last.close.toFixed(4)}}</strong></span>
          <span><span style="color:#555">Date</span> <strong>${{last.time}}</strong></span>
        `;
      }})
      .catch(e => {{ document.getElementById('status').textContent = 'Failed to load: ' + e; }});
    </script>"""

    return page_wrap(f'Chart — {ticker}', '', content)


@app.route('/api/options-lookup/<ticker>')
def api_options_lookup(ticker):
    expiry = request.args.get('expiry', '').strip() or None
    try:
        return jsonify(lookup_chain_on_demand(ticker, expiry))
    except Exception as e:
        return jsonify({'error': str(e)})


@app.route('/api/chart-data/<ticker>')
def chart_data(ticker):
    ticker = ticker.upper()
    try:
        conn = get_connection()
        df = get_ticker_data(conn, ticker)
        conn.close()

        if df is None or df.empty:
            return jsonify({'error': f'No data for {ticker}'})

        # Compute EMAs
        ema5  = df['close'].ewm(span=5,  adjust=False).mean()
        ema26 = df['close'].ewm(span=26, adjust=False).mean()

        def to_time(ts):
            return ts.strftime('%Y-%m-%d')

        ohlcv = [
            {'time': to_time(ts), 'open': float(r['open']), 'high': float(r['high']),
             'low': float(r['low']), 'close': float(r['close'])}
            for ts, r in df.iterrows()
        ]
        volume = [
            {'time': to_time(ts), 'value': float(r['volume']),
             'color': '#22c55e44' if r['close'] >= r['open'] else '#ef444444'}
            for ts, r in df.iterrows()
        ]
        ema5_data  = [{'time': to_time(ts), 'value': float(v)} for ts, v in ema5.items()]
        ema26_data = [{'time': to_time(ts), 'value': float(v)} for ts, v in ema26.items()]

        return jsonify({
            'ticker': ticker,
            'bars': len(df),
            'date_range': f"{to_time(df.index[0])} → {to_time(df.index[-1])}",
            'ohlcv': ohlcv,
            'volume': volume,
            'ema5': ema5_data,
            'ema26': ema26_data,
        })

    except Exception as e:
        return jsonify({'error': str(e)})


# ─── Auth ─────────────────────────────────────────────────────────────────────

@app.route('/login', methods=['GET', 'POST'])
def login():
    error = ''
    if request.method == 'POST':
        if request.form.get('password') in (ADMIN_PASSWORD, JANG_PASSWORD, HODAN_PASSWORD):
            session['admin'] = True
            return redirect('/')
        error = 'Wrong password.'
    return page_wrap('Login', '', f"""
    <div style="max-width:360px;margin:80px auto">
      <section>
        <h2>Admin Login</h2>
        <form method="POST">
          <input name="password" type="password" placeholder="Password" autofocus
            style="width:100%;padding:9px 12px;background:#0a0c14;border:1px solid #2a2d3e;
                   border-radius:6px;color:#fff;font-size:.95rem;margin-bottom:12px">
          {'<p style="color:#f87171;font-size:.82rem;margin-bottom:10px">' + error + '</p>' if error else ''}
          <button type="submit" class="btn btn-blue" style="width:100%">Login</button>
        </form>
      </section>
    </div>""")


@app.route('/logout')
def logout():
    session.pop('admin', None)
    return redirect('/')


@app.route('/deploy-webhook', methods=['POST'])
def deploy_webhook():
    """GitHub push webhook: git pull the repo, then touch the WSGI file to reload."""
    signature = request.headers.get('X-Hub-Signature-256', '')
    expected = 'sha256=' + hmac.new(GITHUB_WEBHOOK_SECRET.encode(), request.data, hashlib.sha256).hexdigest()
    if not hmac.compare_digest(signature, expected):
        return 'Invalid signature', 403

    log_path = os.path.join(BASE_DIR, 'deploy_log.txt')
    result = subprocess.run(['git', 'pull', 'origin', 'main'], cwd=REPO_DIR,
                             capture_output=True, text=True, timeout=60)
    with open(log_path, 'w') as f:
        f.write(f"{datetime.now()}\nSTDOUT:\n{result.stdout}\nSTDERR:\n{result.stderr}\n")

    if result.returncode != 0:
        return 'git pull failed', 500

    try:
        os.utime(WSGI_RELOAD_FILE, None)
    except Exception as e:
        with open(log_path, 'a') as f:
            f.write(f"\nReload touch failed: {e}\n")
        return 'pulled but reload failed', 500

    return 'OK', 200


# ─── Data actions ─────────────────────────────────────────────────────────────

REFRESH_DATE_FILE = os.path.join(BASE_DIR, 'last_refresh_date.txt')


def get_last_refresh_date():
    """Return the date string of the last successful refresh, or None."""
    try:
        with open(REFRESH_DATE_FILE) as f:
            return f.read().strip()
    except Exception:
        return None


def set_last_refresh_date():
    from datetime import date
    with open(REFRESH_DATE_FILE, 'w') as f:
        f.write(date.today().isoformat())


def already_refreshed_today():
    from datetime import date
    return get_last_refresh_date() == date.today().isoformat()


# Full daily update (db_daily_update.py — all ~3,400 tickers) is tracked
# separately from the picks-only refresh above, since it's a distinct,
# much heavier job. Used by the auto-update-on-open check below.
DAILY_UPDATE_DATE_FILE = os.path.join(BASE_DIR, 'last_daily_update_date.txt')


def get_last_daily_update_date():
    """Return the date string of the last successful full daily update, or None."""
    try:
        with open(DAILY_UPDATE_DATE_FILE) as f:
            return f.read().strip()
    except Exception:
        return None


def set_last_daily_update_date():
    from datetime import date
    with open(DAILY_UPDATE_DATE_FILE, 'w') as f:
        f.write(date.today().isoformat())


def already_daily_updated_today():
    from datetime import date
    return get_last_daily_update_date() == date.today().isoformat()


def _run_refresh_job():
    """Update prices only for tickers with open positions (US + ASX). Fast."""
    global _job_running, _job_name
    import yfinance as yf
    from datetime import date, timedelta

    def log(msg):
        with open(LOG_FILE, 'a') as f:
            f.write(msg)

    with open(LOG_FILE, 'w') as f:
        f.write(f"=== Picks Price Refresh ===\nStarted: {datetime.now()}\n\n")
    try:
        conn = get_connection()

        # ── US open positions ─────────────────────────────────────────────────
        with conn.cursor() as cur:
            cur.execute("SELECT DISTINCT ticker FROM jimmy_picks WHERE status='open'")
            us_tickers = [r[0] for r in cur.fetchall()]

        log(f"US open positions: {', '.join(us_tickers) if us_tickers else 'none'}\n")
        for ticker in us_tickers:
            try:
                with conn.cursor() as cur:
                    cur.execute("SELECT MAX(date) FROM prices WHERE ticker=%s", (ticker,))
                    last = cur.fetchone()[0]
                start = (last + timedelta(days=1)) if last else (date.today() - timedelta(days=365))
                end   = date.today() + timedelta(days=1)
                df    = yf.download(ticker, start=start, end=end,
                                    interval='1d', auto_adjust=True, progress=False)
                if df.empty:
                    log(f"  {ticker}: no new data\n")
                    continue
                if hasattr(df.columns, 'get_level_values'):
                    df.columns = df.columns.get_level_values(0)
                rows = []
                for dt, row in df.iterrows():
                    rows.append((ticker.upper(), str(dt.date()),
                                 float(row['Open']), float(row['High']),
                                 float(row['Low']),  float(row['Close']),
                                 int(row['Volume']) if not pd.isna(row['Volume']) else 0))
                with conn.cursor() as cur:
                    cur.executemany("""
                        INSERT INTO prices (ticker,date,open,high,low,close,volume)
                        VALUES (%s,%s,%s,%s,%s,%s,%s)
                        ON DUPLICATE KEY UPDATE
                          open=VALUES(open),high=VALUES(high),low=VALUES(low),
                          close=VALUES(close),volume=VALUES(volume)
                    """, rows)
                conn.commit()
                log(f"  {ticker}: updated {len(rows)} rows\n")
            except Exception as e:
                log(f"  {ticker}: ERROR — {e}\n")

        # ── ASX open positions ────────────────────────────────────────────────
        with conn.cursor() as cur:
            cur.execute("SELECT DISTINCT ticker FROM asx_picks WHERE status='open'")
            asx_tickers = [r[0] for r in cur.fetchall()]

        log(f"\nASX open positions: {', '.join(asx_tickers) if asx_tickers else 'none'}\n")
        for ticker in asx_tickers:
            try:
                with conn.cursor() as cur:
                    cur.execute("SELECT MAX(date) FROM asx_prices WHERE ticker=%s", (ticker,))
                    last = cur.fetchone()[0]
                start    = (last + timedelta(days=1)) if last else (date.today() - timedelta(days=365))
                end      = date.today() + timedelta(days=1)
                yf_ticker = ticker + '.AX'
                df = yf.download(yf_ticker, start=start, end=end,
                                 interval='1d', auto_adjust=True, progress=False)
                if df.empty:
                    log(f"  {ticker}: no new data\n")
                    continue
                if hasattr(df.columns, 'get_level_values'):
                    df.columns = df.columns.get_level_values(0)
                rows = []
                for dt, row in df.iterrows():
                    rows.append((ticker.upper(), str(dt.date()),
                                 float(row['Open']), float(row['High']),
                                 float(row['Low']),  float(row['Close']),
                                 int(row['Volume']) if not pd.isna(row['Volume']) else 0))
                with conn.cursor() as cur:
                    cur.executemany("""
                        INSERT INTO asx_prices (ticker,date,open,high,low,close,volume)
                        VALUES (%s,%s,%s,%s,%s,%s,%s)
                        ON DUPLICATE KEY UPDATE
                          open=VALUES(open),high=VALUES(high),low=VALUES(low),
                          close=VALUES(close),volume=VALUES(volume)
                    """, rows)
                conn.commit()
                log(f"  {ticker}: updated {len(rows)} rows\n")
            except Exception as e:
                log(f"  {ticker}: ERROR — {e}\n")

        conn.close()

        # ── Real options chains for tickers used on the options pages ──────────
        log(f"\nOptions chains (real data, US-listed only):\n")
        try:
            refresh_all_relevant_chains(log=log)
        except Exception as e:
            log(f"  ERROR — {e}\n")

        set_last_refresh_date()
        log(f"\nDone: {datetime.now()}\n")

    except Exception as e:
        log(f"\nFATAL ERROR: {e}\n")
    finally:
        with _job_lock:
            _job_running = False
            _job_name    = ''


def start_refresh_job():
    global _job_running, _job_name
    with _job_lock:
        if _job_running:
            return False
        _job_running = True
        _job_name    = 'Data Refresh'
    threading.Thread(target=_run_refresh_job, daemon=True).start()
    return True


@app.route('/run-refresh')
def run_refresh():
    if not is_admin():
        return redirect('/')
    start_refresh_job()
    return redirect('/admin')


def _run_daily_update_job():
    """
    Run db_daily_update.py (full ~3,400-ticker refresh) as a subprocess,
    same mechanics as _run_script, but marks today as done on a clean exit
    so already_daily_updated_today() reflects it — used both by the manual
    'Run Daily Update' button and the auto-update-on-open check.
    """
    global _job_running, _job_name, _job_auto
    with open(LOG_FILE, 'w') as f:
        f.write(f"=== Daily Update ===\nStarted: {datetime.now()}\n\n")
    try:
        proc = subprocess.Popen(
            [PYTHON, '-u', os.path.join(BASE_DIR, 'db_daily_update.py')],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, cwd=BASE_DIR
        )
        with open(LOG_FILE, 'a') as f:
            for line in proc.stdout:
                f.write(line)
                f.flush()
        proc.wait()
        with open(LOG_FILE, 'a') as f:
            f.write(f"\nFinished: {datetime.now()}\nExit code: {proc.returncode}\n")
        if proc.returncode == 0:
            set_last_daily_update_date()
    except Exception as e:
        with open(LOG_FILE, 'a') as f:
            f.write(f"\nERROR: {e}\n")
    finally:
        with _job_lock:
            _job_running = False
            _job_name    = ''
            _job_auto    = False


def start_daily_update_job(auto=False):
    global _job_running, _job_name, _job_auto
    with _job_lock:
        if _job_running:
            return False
        _job_running = True
        _job_name    = 'Daily Update'
        _job_auto    = auto
    threading.Thread(target=_run_daily_update_job, daemon=True).start()
    return True


def maybe_auto_daily_update():
    """
    Auto-update-on-open check: if an admin is logged in, no job is already
    running, and the full daily update hasn't completed yet today, kick it
    off in the background — same job as the manual 'Run Daily Update'
    button, just triggered by opening a page instead of clicking. Silent,
    best-effort: never raises, never blocks the request.
    """
    try:
        if not is_admin():
            return
        with _job_lock:
            running = _job_running
        if running or already_daily_updated_today():
            return
        start_daily_update_job(auto=True)
    except Exception:
        pass


@app.before_request
def _auto_daily_update_check():
    maybe_auto_daily_update()


@app.route('/run-daily')
def run_daily():
    if not is_admin():
        return redirect('/')
    start_daily_update_job()
    return redirect('/admin')


@app.route('/run-initial')
def run_initial():
    if not is_admin():
        return redirect('/')
    start_script_job(os.path.join(BASE_DIR, 'db_initial_download.py'), 'Initial Download')
    return redirect('/admin')


# ─── Log view ─────────────────────────────────────────────────────────────────

@app.route('/log-view')
def log_view():
    with _job_lock:
        running = _job_running
    log = get_log().replace('<', '&lt;').replace('>', '&gt;')
    content = f'<section><h2>Last Run Log</h2><pre>{log}</pre></section>'
    return page_wrap('Log', 'log', content, auto_refresh=running)


@app.route('/status')
def status():
    with _job_lock:
        return jsonify({'running': _job_running, 'job': _job_name})


# ─── Jimmy's Stock Picks ──────────────────────────────────────────────────────

@app.route('/picks')
def picks_page():
    positions = get_positions()
    history   = get_history()
    cash      = get_account()
    port_val  = get_portfolio_value(positions)
    total_val = cash + port_val
    total_pnl = total_val - 100_000.0

    # Daily P&L — compare today's close vs yesterday's close for each position
    daily_changes = get_daily_changes([p['ticker'] for p in positions])
    daily_pnl_total = sum(
        p['shares'] * (daily_changes[p['ticker']][0] - daily_changes[p['ticker']][1])
        for p in positions if p['ticker'] in daily_changes
    )
    for p in positions:
        if p['ticker'] in daily_changes:
            today, prev = daily_changes[p['ticker']]
            p['daily_pnl'] = p['shares'] * (today - prev)
            p['daily_pct'] = ((today - prev) / prev * 100) if prev else 0
        else:
            p['daily_pnl'] = 0.0
            p['daily_pct'] = 0.0

    # Account summary bar
    pnl_color  = '#22c55e' if total_pnl >= 0 else '#ef4444'
    pnl_sign   = '+' if total_pnl >= 0 else ''
    dpnl_color = '#22c55e' if daily_pnl_total >= 0 else '#ef4444'
    dpnl_sign  = '+' if daily_pnl_total >= 0 else ''
    summary = f"""
    <div class="grid4" style="margin-bottom:24px">
      <div class="card">
        <div class="stat-label">Cash Available</div>
        <div class="stat-value" style="font-size:1.3rem">${cash:,.2f}</div>
        <div class="stat-sub">of $100,000 starting balance</div>
      </div>
      <div class="card">
        <div class="stat-label">Portfolio Value</div>
        <div class="stat-value" style="font-size:1.3rem">${port_val:,.2f}</div>
        <div class="stat-sub">{len(positions)} open position{'s' if len(positions)!=1 else ''}</div>
      </div>
      <div class="card">
        <div class="stat-label">Total P&amp;L</div>
        <div class="stat-value" style="font-size:1.3rem;color:{pnl_color}">{pnl_sign}${total_pnl:,.2f}</div>
        <div class="stat-sub" style="color:{pnl_color}">{pnl_sign}{total_pnl/1000:.1f}% on $100k</div>
      </div>
      <div class="card">
        <div class="stat-label">Today's P&amp;L</div>
        <div class="stat-value" style="font-size:1.3rem;color:{dpnl_color}">{dpnl_sign}${daily_pnl_total:,.2f}</div>
        <div class="stat-sub" style="color:{dpnl_color}">unrealised daily move</div>
      </div>
    </div>"""

    # Add new pick form (admin only)
    add_form = '' if not is_admin() else """
    <section>
      <h2>Add New Pick</h2>
      <form method="POST" action="/picks/buy" enctype="multipart/form-data">
        <div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(180px,1fr));gap:12px;margin-bottom:12px">
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Ticker *</label>
            <input name="ticker" placeholder="e.g. AAPL" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Shares *</label>
            <input name="shares" type="number" step="0.0001" placeholder="e.g. 100" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Buy Price (USD) *</label>
            <input name="buy_price" type="number" step="0.0001" placeholder="e.g. 150.00" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Target / Take Profit</label>
            <input name="target_price" type="number" step="0.0001" placeholder="e.g. 200.00" style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Trading Style *</label>
            <select name="style" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
              """ + ''.join(f'<option value="{key}">{label}</option>' for key, label in STYLES.items()) + """
            </select>
          </div>
        </div>
        <div style="margin-bottom:12px">
          <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Why I think it will go up</label>
          <textarea name="reason" rows="3" placeholder="Channel breakout forming, EMA squeeze on weekly..." style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.88rem;resize:vertical"></textarea>
        </div>
        <div style="margin-bottom:16px">
          <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">TradingView Chart Screenshot</label>
          <input name="chart_image" type="file" accept="image/*" style="color:#aaa;font-size:.85rem">
        </div>
        <button type="submit" class="btn btn-green">+ Add to Portfolio</button>
      </form>
    </section>"""

    # Style filter tabs
    style_filter = request.args.get('style', 'all')
    filtered_positions = positions if style_filter == 'all' else [p for p in positions if p['style'] == style_filter]
    tab_defs = [('all', 'All')] + list(STYLES.items())
    tabs_html = '<div style="display:flex;gap:8px;flex-wrap:wrap;margin-bottom:16px">'
    for key, label in tab_defs:
        active = 'background:#3b82f6;color:#fff' if key == style_filter else 'background:#1a1d2e;color:#aaa'
        tabs_html += f'<a href="/picks?style={key}" style="padding:6px 14px;border-radius:20px;font-size:.82rem;text-decoration:none;{active}">{label}</a>'
    tabs_html += '</div>'

    # Open positions
    pos_html = ''
    if positions:
        cards = ''
        for p in filtered_positions:
            pnl_c  = '#22c55e' if p['pnl'] >= 0 else '#ef4444'
            sign   = '+' if p['pnl'] >= 0 else ''
            tgt    = f"${fmt_num(p['target_price'])}" if p['target_price'] else '—'
            upside = ''
            if p['target_price']:
                up = (p['target_price'] - p['current_price']) / p['current_price'] * 100
                upside = f"<span style='color:#60a5fa;font-size:.78rem'>({up:+.1f}% to target)</span>"

            style_badge = f'<span style="font-size:.72rem;color:#a78bfa;background:#a78bfa18;padding:2px 8px;border-radius:4px;margin-left:8px">{STYLES.get(p["style"], p["style"])}</span>'

            img_html = ''
            if p['image_path']:
                img_html = f'<img src="/picks/image/{p["image_path"]}" style="width:100%;border-radius:6px;margin-bottom:12px;border:1px solid #2a2d3e">'

            reason_html = f'<p style="color:#aaa;font-size:.83rem;margin-bottom:12px;line-height:1.5">{p["reason"]}</p>' if p['reason'] else ''

            if is_admin():
                pticker = p['ticker']
                action_html = f"""
                <div style="display:flex;gap:8px;align-items:center">
                  <button class="btn btn-amber" style="padding:7px 16px"
                    onclick="openSellModal({p['id']},'{pticker}',{p['shares']},{p['current_price']:.4f},'/picks/sell/{p['id']}')">Sell</button>
                  <a href="/chart/{pticker}" class="btn btn-blue" style="padding:7px 14px;font-size:.82rem">Chart</a>
                </div>"""
            else:
                action_html = f'<a href="/chart/{p["ticker"]}" class="btn btn-blue" style="padding:7px 14px;font-size:.82rem">View Chart</a>'

            dc     = p['daily_pnl']
            dc_c   = '#22c55e' if dc >= 0 else '#ef4444'
            dc_s   = '+' if dc >= 0 else ''
            daily_badge = f'<span style="font-size:.78rem;font-weight:600;color:{dc_c};background:{dc_c}18;padding:2px 8px;border-radius:4px">{dc_s}${dc:,.2f} today ({dc_s}{p["daily_pct"]:.2f}%)</span>'

            cards += f"""
            <div class="card" style="margin-bottom:16px">
              <div style="display:flex;justify-content:space-between;align-items:flex-start;flex-wrap:wrap;gap:8px;margin-bottom:8px">
                <div>
                  <a href="/chart/{p['ticker']}" style="font-size:1.3rem;font-weight:700;color:#60a5fa">{p['ticker']}</a>
                  <span style="color:#555;font-size:.78rem;margin-left:10px">bought {p['bought_date']}</span>
                  {style_badge}
                </div>
                <span style="font-size:1.1rem;font-weight:700;color:{pnl_c}">{sign}${p['pnl']:,.2f} ({sign}{p['pnl_pct']:.1f}%)</span>
              </div>
              <div style="margin-bottom:12px">{daily_badge}</div>
              {img_html}
              {reason_html}
              <div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(130px,1fr));gap:8px;margin-bottom:14px;font-size:.83rem">
                <div><span style="color:#555">Shares</span><br><strong>{fmt_num(p['shares'])}</strong></div>
                <div><span style="color:#555">Buy Price</span><br><strong>${fmt_num(p['buy_price'])}</strong></div>
                <div><span style="color:#555">Current</span><br><strong>${fmt_num(p['current_price'])}</strong></div>
                <div><span style="color:#555">Cost Basis</span><br><strong>${p['cost']:,.2f}</strong></div>
                <div><span style="color:#555">Market Value</span><br><strong>${p['value']:,.2f}</strong></div>
                <div><span style="color:#555">Target</span><br><strong>{tgt}</strong> {upside}</div>
              </div>
              {action_html}
            </div>"""
        if filtered_positions:
            pos_html = f'<section><h2>Open Positions ({len(filtered_positions)})</h2>{cards}</section>'
        else:
            pos_html = '<section><h2>Open Positions</h2><p class="note">No open positions for this style.</p></section>'
    else:
        pos_html = '<section><h2>Open Positions</h2><p class="note">No open positions yet. Add your first pick above!</p></section>'

    # Trade history
    hist_html = ''
    if history:
        rows = ''
        for t in history:
            action_color = '#22c55e' if t['action'] == 'BUY' else '#ef4444'
            pnl_str = ''
            if t['pnl'] is not None:
                pnl_color = '#22c55e' if t['pnl'] >= 0 else '#ef4444'
                pnl_str = f'<span style="color:{pnl_color}">{("+" if t["pnl"]>=0 else "")}${t["pnl"]:,.2f}</span>'
            rows += f"""<tr>
              <td>{t['trade_date']}</td>
              <td><strong style="color:#60a5fa">{t['ticker']}</strong></td>
              <td><span style="color:{action_color};font-weight:700">{t['action']}</span></td>
              <td>{fmt_num(t['shares'])}</td>
              <td>${fmt_num(t['price'])}</td>
              <td>${t['total']:,.2f}</td>
              <td>{pnl_str}</td>
            </tr>"""
        hist_html = f"""
        <section>
          <h2>Trade History</h2>
          <style>
            table{{width:100%;border-collapse:collapse;font-size:.83rem}}
            th{{text-align:left;padding:8px 10px;color:#555;border-bottom:1px solid #2a2d3e;font-weight:500}}
            td{{padding:8px 10px;border-bottom:1px solid #151820}}
            tr:hover td{{background:#1f2235}}
          </style>
          <table>
            <tr><th>Date</th><th>Ticker</th><th>Action</th><th>Shares</th><th>Price</th><th>Total</th><th>P&L</th></tr>
            {rows}
          </table>
        </section>"""

    msg = request.args.get('msg', '')
    msg_html = f'<div style="background:#1a2e1a;border:1px solid #22c55e;border-radius:8px;padding:12px 16px;margin-bottom:20px;color:#86efac">{msg}</div>' if msg else ''
    err = request.args.get('err', '')
    err_html = f'<div class="err-box">{err}</div>' if err else ''

    sell_modal = """
    <div id="sell-modal" style="display:none;position:fixed;inset:0;background:rgba(0,0,0,.75);z-index:9000;align-items:center;justify-content:center">
      <div style="background:#13151f;border:1px solid #2a2d3e;border-radius:12px;padding:28px;width:100%;max-width:500px;margin:20px">
        <h3 id="sell-modal-title" style="margin:0 0 20px">Sell Position</h3>
        <form id="sell-form" method="POST" enctype="multipart/form-data">
          <div style="margin-bottom:14px">
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Sell Price *</label>
            <input id="sell-price-input" name="sell_price" type="number" step="0.0001" required
              style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div style="margin-bottom:14px">
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Why I sold</label>
            <textarea name="sell_reason" rows="4" placeholder="Stop loss hit, thesis broke, took profit at target..."
              style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.88rem;resize:vertical"></textarea>
          </div>
          <div style="margin-bottom:20px">
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Chart Screenshot (sell setup)</label>
            <input name="sell_chart" type="file" accept="image/*" style="color:#aaa;font-size:.85rem">
          </div>
          <div style="display:flex;gap:10px">
            <button type="submit" class="btn btn-amber" style="flex:1">Confirm Sell</button>
            <button type="button" class="btn" style="flex:1;background:#252839" onclick="closeSellModal()">Cancel</button>
          </div>
        </form>
      </div>
    </div>
    <script>
    function openSellModal(pickId, ticker, shares, currentPrice, action) {
      document.getElementById('sell-modal-title').textContent = 'Sell ' + shares + ' shares of ' + ticker;
      document.getElementById('sell-price-input').value = currentPrice;
      document.getElementById('sell-form').action = action;
      document.getElementById('sell-modal').style.display = 'flex';
    }
    function closeSellModal() {
      document.getElementById('sell-modal').style.display = 'none';
    }
    document.addEventListener('keydown', function(e) {
      if (e.key === 'Escape') closeSellModal();
    });
    </script>"""

    content = err_html + msg_html + summary + add_form + tabs_html + pos_html + hist_html + sell_modal
    return page_wrap("Jimmy's Picks", 'picks', content)


@app.route('/picks/buy', methods=['POST'])
def picks_buy():
    ticker     = request.form.get('ticker', '').strip().upper()
    shares     = float(request.form.get('shares', 0))
    buy_price  = float(request.form.get('buy_price', 0))
    target     = request.form.get('target_price', '').strip()
    reason     = request.form.get('reason', '').strip()
    style      = request.form.get('style', 'swing_pullback').strip()
    target_val = float(target) if target else None

    # Handle image upload
    image_filename = ''
    file = request.files.get('chart_image')
    if file and file.filename:
        ext = os.path.splitext(file.filename)[1].lower()
        image_filename = f"{ticker}_{uuid.uuid4().hex[:8]}{ext}"
        os.makedirs(UPLOADS_DIR, exist_ok=True)
        file.save(os.path.join(UPLOADS_DIR, image_filename))

    ok, result = buy_stock(ticker, shares, buy_price, target_val, reason, image_filename, style)
    if ok:
        return redirect(f'/picks?msg=Bought+{shares}+shares+of+{ticker}+at+${buy_price:.4f}')
    else:
        return redirect(f'/picks?err={result}')


@app.route('/picks/sell/<int:pick_id>', methods=['POST'])
def picks_sell(pick_id):
    if not is_admin():
        return redirect('/picks')
    sell_price  = float(request.form.get('sell_price', 0))
    sell_reason = request.form.get('sell_reason', '').strip()

    sell_image = ''
    file = request.files.get('sell_chart')
    if file and file.filename:
        ext = os.path.splitext(file.filename)[1].lower()
        sell_image = f"sell_{pick_id}_{uuid.uuid4().hex[:8]}{ext}"
        os.makedirs(UPLOADS_DIR, exist_ok=True)
        file.save(os.path.join(UPLOADS_DIR, sell_image))

    ok, result = sell_stock(pick_id, sell_price, sell_reason, sell_image)
    if ok:
        sign = '+' if result >= 0 else ''
        return redirect(f'/picks?msg=Position+closed.+P%26L:+{sign}${result:.2f}')
    else:
        return redirect(f'/picks?err={result}')


@app.route('/picks/image/<filename>')
def picks_image(filename):
    return send_from_directory(UPLOADS_DIR, filename)


# ─── Jimmy's Ideas ($10k-per-idea call tracker, 3 systems) ───────────────────

@app.route('/ideas')
def ideas_page():
    open_ideas   = get_open_ideas()
    closed_ideas = get_closed_ideas()
    summary      = get_system_summary()

    daily_changes = get_daily_changes([i['ticker'] for i in open_ideas])
    for i in open_ideas:
        if i['ticker'] in daily_changes:
            today, prev = daily_changes[i['ticker']]
            i['daily_pnl'] = i['shares'] * (today - prev)
            i['daily_pct'] = ((today - prev) / prev * 100) if prev else 0
        else:
            i['daily_pnl'] = 0.0
            i['daily_pct'] = 0.0

    # Per-system summary cards
    sys_cards = ''
    for key, label in STYLES.items():
        s = summary[key]
        c = '#22c55e' if s['total_pnl'] >= 0 else '#ef4444'
        sign = '+' if s['total_pnl'] >= 0 else ''
        wr = f"{s['win_rate']:.0f}% win rate" if s['win_rate'] is not None else 'no closed ideas yet'
        sys_cards += f"""
        <div class="card">
          <div class="stat-label">{label}</div>
          <div class="stat-value" style="font-size:1.3rem;color:{c}">{sign}${s['total_pnl']:,.2f}</div>
          <div class="stat-sub">{s['open']} open &middot; {s['closed']} closed &middot; {wr}</div>
        </div>"""
    summary_html = f'<div class="grid4" style="margin-bottom:24px">{sys_cards}</div>'

    # Add new idea form (admin only) — no shares field, always sized at $10k
    add_form = '' if not is_admin() else f"""
    <section>
      <h2>Post New Idea</h2>
      <p class="note" style="margin-bottom:12px">Every idea is sized as a fixed ${IDEA_NOTIONAL:,.0f} hypothetical buy-in — no shares to enter, just the entry price.</p>
      <form method="POST" action="/ideas/post" enctype="multipart/form-data">
        <div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(180px,1fr));gap:12px;margin-bottom:12px">
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Ticker *</label>
            <input name="ticker" placeholder="e.g. AAPL" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Entry Price (USD) *</label>
            <input name="buy_price" type="number" step="0.0001" placeholder="e.g. 150.00" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">System *</label>
            <select name="style" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
              """ + ''.join(f'<option value="{key}">{label}</option>' for key, label in STYLES.items()) + """
            </select>
          </div>
        </div>
        <div style="margin-bottom:12px">
          <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Why this idea</label>
          <textarea name="reason" rows="3" placeholder="Gap down onto prior support, channel bottom..." style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.88rem;resize:vertical"></textarea>
        </div>
        <div style="margin-bottom:16px">
          <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Chart Screenshot</label>
          <input name="chart_image" type="file" accept="image/*" style="color:#aaa;font-size:.85rem">
        </div>
        <button type="submit" class="btn btn-green">+ Post Idea</button>
      </form>
    </section>"""

    # System filter tabs
    style_filter = request.args.get('style', 'all')
    filtered_open = open_ideas if style_filter == 'all' else [i for i in open_ideas if i['style'] == style_filter]
    tab_defs = [('all', 'All')] + list(STYLES.items())
    tabs_html = '<div style="display:flex;gap:8px;flex-wrap:wrap;margin-bottom:16px">'
    for key, label in tab_defs:
        active = 'background:#3b82f6;color:#fff' if key == style_filter else 'background:#1a1d2e;color:#aaa'
        tabs_html += f'<a href="/ideas?style={key}" style="padding:6px 14px;border-radius:20px;font-size:.82rem;text-decoration:none;{active}">{label}</a>'
    tabs_html += '</div>'

    # Open ideas
    if open_ideas:
        cards = ''
        for i in filtered_open:
            pnl_c = '#22c55e' if i['pnl'] >= 0 else '#ef4444'
            sign  = '+' if i['pnl'] >= 0 else ''
            style_badge = f'<span style="font-size:.72rem;color:#a78bfa;background:#a78bfa18;padding:2px 8px;border-radius:4px;margin-left:8px">{STYLES.get(i["style"], i["style"])}</span>'

            img_html = ''
            if i['image_path']:
                img_html = f'<img src="/ideas/image/{i["image_path"]}" style="width:100%;border-radius:6px;margin-bottom:12px;border:1px solid #2a2d3e">'
            reason_html = f'<p style="color:#aaa;font-size:.83rem;margin-bottom:12px;line-height:1.5">{i["reason"]}</p>' if i['reason'] else ''

            if is_admin():
                action_html = f"""
                <div style="display:flex;gap:8px;align-items:center">
                  <button class="btn btn-amber" style="padding:7px 16px"
                    onclick="openIdeaCloseModal({i['id']},'{i['ticker']}',{i['current_price']:.4f},'/ideas/close/{i['id']}')">Close</button>
                  <a href="/chart/{i['ticker']}" class="btn btn-blue" style="padding:7px 14px;font-size:.82rem">Chart</a>
                </div>"""
            else:
                action_html = f'<a href="/chart/{i["ticker"]}" class="btn btn-blue" style="padding:7px 14px;font-size:.82rem">View Chart</a>'

            dc   = i['daily_pnl']
            dc_c = '#22c55e' if dc >= 0 else '#ef4444'
            dc_s = '+' if dc >= 0 else ''
            daily_badge = f'<span style="font-size:.78rem;font-weight:600;color:{dc_c};background:{dc_c}18;padding:2px 8px;border-radius:4px">{dc_s}${dc:,.2f} today ({dc_s}{i["daily_pct"]:.2f}%)</span>'

            cards += f"""
            <div class="card" style="margin-bottom:16px">
              <div style="display:flex;justify-content:space-between;align-items:flex-start;flex-wrap:wrap;gap:8px;margin-bottom:8px">
                <div>
                  <a href="/chart/{i['ticker']}" style="font-size:1.3rem;font-weight:700;color:#60a5fa">{i['ticker']}</a>
                  <span style="color:#555;font-size:.78rem;margin-left:10px">posted {i['posted_date']}</span>
                  {style_badge}
                </div>
                <span style="font-size:1.1rem;font-weight:700;color:{pnl_c}">{sign}${i['pnl']:,.2f} ({sign}{i['pnl_pct']:.1f}%)</span>
              </div>
              <div style="margin-bottom:12px">{daily_badge}</div>
              {img_html}
              {reason_html}
              <div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(130px,1fr));gap:8px;margin-bottom:14px;font-size:.83rem">
                <div><span style="color:#555">${IDEA_NOTIONAL:,.0f} buy-in</span><br><strong>{fmt_num(i['shares'])} sh</strong></div>
                <div><span style="color:#555">Entry</span><br><strong>${fmt_num(i['buy_price'])}</strong></div>
                <div><span style="color:#555">Current</span><br><strong>${fmt_num(i['current_price'])}</strong></div>
                <div><span style="color:#555">Worth Now</span><br><strong>${i['value']:,.2f}</strong></div>
              </div>
              {action_html}
            </div>"""
        if filtered_open:
            pos_html = f'<section><h2>Open Ideas ({len(filtered_open)})</h2>{cards}</section>'
        else:
            pos_html = '<section><h2>Open Ideas</h2><p class="note">No open ideas for this system.</p></section>'
    else:
        pos_html = '<section><h2>Open Ideas</h2><p class="note">No ideas posted yet.</p></section>'

    # Closed ideas — the track record
    filtered_closed = closed_ideas if style_filter == 'all' else [i for i in closed_ideas if i['style'] == style_filter]
    hist_html = ''
    if filtered_closed:
        rows = ''
        for i in filtered_closed:
            pnl_c = '#22c55e' if i['pnl'] >= 0 else '#ef4444'
            sign  = '+' if i['pnl'] >= 0 else ''
            del_btn = f'<a href="/ideas/delete/{i["id"]}" onclick="return confirm(\'Delete this closed idea?\')" style="color:#555;font-size:.78rem">delete</a>' if is_admin() else ''
            rows += f"""<tr>
              <td>{i['posted_date']} → {i['sell_date']}</td>
              <td><strong style="color:#60a5fa">{i['ticker']}</strong></td>
              <td>{STYLES.get(i['style'], i['style'])}</td>
              <td>${fmt_num(i['buy_price'])}</td>
              <td>${fmt_num(i['sell_price'])}</td>
              <td style="color:{pnl_c};font-weight:700">{sign}${i['pnl']:,.2f} ({sign}{i['pnl_pct']:.1f}%)</td>
              <td>{del_btn}</td>
            </tr>"""
        hist_html = f"""
        <section>
          <h2>Closed Ideas ({len(filtered_closed)})</h2>
          <style>
            table{{width:100%;border-collapse:collapse;font-size:.83rem}}
            th{{text-align:left;padding:8px 10px;color:#555;border-bottom:1px solid #2a2d3e;font-weight:500}}
            td{{padding:8px 10px;border-bottom:1px solid #151820}}
            tr:hover td{{background:#1f2235}}
          </style>
          <table>
            <tr><th>Posted → Closed</th><th>Ticker</th><th>System</th><th>Entry</th><th>Exit</th><th>P&amp;L</th><th></th></tr>
            {rows}
          </table>
        </section>"""

    msg = request.args.get('msg', '')
    msg_html = f'<div style="background:#1a2e1a;border:1px solid #22c55e;border-radius:8px;padding:12px 16px;margin-bottom:20px;color:#86efac">{msg}</div>' if msg else ''
    err = request.args.get('err', '')
    err_html = f'<div class="err-box">{err}</div>' if err else ''

    close_modal = """
    <div id="idea-close-modal" style="display:none;position:fixed;inset:0;background:rgba(0,0,0,.75);z-index:9000;align-items:center;justify-content:center">
      <div style="background:#13151f;border:1px solid #2a2d3e;border-radius:12px;padding:28px;width:100%;max-width:500px;margin:20px">
        <h3 id="idea-close-modal-title" style="margin:0 0 20px">Close Idea</h3>
        <form id="idea-close-form" method="POST" enctype="multipart/form-data">
          <div style="margin-bottom:14px">
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Exit Price *</label>
            <input id="idea-close-price-input" name="sell_price" type="number" step="0.0001" required
              style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div style="margin-bottom:14px">
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Why closed</label>
            <textarea name="sell_reason" rows="4" placeholder="Target hit, thesis broke, stop out..."
              style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.88rem;resize:vertical"></textarea>
          </div>
          <div style="margin-bottom:20px">
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Chart Screenshot</label>
            <input name="sell_chart" type="file" accept="image/*" style="color:#aaa;font-size:.85rem">
          </div>
          <div style="display:flex;gap:10px">
            <button type="submit" class="btn btn-amber" style="flex:1">Confirm Close</button>
            <button type="button" class="btn" style="flex:1;background:#252839" onclick="closeIdeaCloseModal()">Cancel</button>
          </div>
        </form>
      </div>
    </div>
    <script>
    function openIdeaCloseModal(ideaId, ticker, currentPrice, action) {
      document.getElementById('idea-close-modal-title').textContent = 'Close ' + ticker;
      document.getElementById('idea-close-price-input').value = currentPrice;
      document.getElementById('idea-close-form').action = action;
      document.getElementById('idea-close-modal').style.display = 'flex';
    }
    function closeIdeaCloseModal() {
      document.getElementById('idea-close-modal').style.display = 'none';
    }
    document.addEventListener('keydown', function(e) {
      if (e.key === 'Escape') closeIdeaCloseModal();
    });
    </script>"""

    content = err_html + msg_html + summary_html + add_form + tabs_html + pos_html + hist_html + close_modal
    return page_wrap("Jimmy's Ideas", 'ideas', content)


@app.route('/ideas/post', methods=['POST'])
def ideas_post():
    if not is_admin():
        return redirect('/ideas')
    ticker    = request.form.get('ticker', '').strip().upper()
    buy_price = request.form.get('buy_price', 0)
    style     = request.form.get('style', 'swing_pullback').strip()
    reason    = request.form.get('reason', '').strip()

    image_filename = ''
    file = request.files.get('chart_image')
    if file and file.filename:
        ext = os.path.splitext(file.filename)[1].lower()
        image_filename = f"idea_{ticker}_{uuid.uuid4().hex[:8]}{ext}"
        os.makedirs(UPLOADS_DIR, exist_ok=True)
        file.save(os.path.join(UPLOADS_DIR, image_filename))

    try:
        buy_price = float(buy_price)
    except (TypeError, ValueError):
        return redirect('/ideas?err=Invalid+entry+price')

    ok, result = post_idea(ticker, buy_price, style, reason, image_filename)
    if ok:
        return redirect(f'/ideas?msg=Posted+{ticker}+idea+at+${buy_price:.4f}')
    else:
        return redirect(f'/ideas?err={result}')


@app.route('/ideas/close/<int:idea_id>', methods=['POST'])
def ideas_close(idea_id):
    if not is_admin():
        return redirect('/ideas')
    sell_price  = request.form.get('sell_price', 0)
    sell_reason = request.form.get('sell_reason', '').strip()

    sell_image = ''
    file = request.files.get('sell_chart')
    if file and file.filename:
        ext = os.path.splitext(file.filename)[1].lower()
        sell_image = f"idea_close_{idea_id}_{uuid.uuid4().hex[:8]}{ext}"
        os.makedirs(UPLOADS_DIR, exist_ok=True)
        file.save(os.path.join(UPLOADS_DIR, sell_image))

    try:
        sell_price = float(sell_price)
    except (TypeError, ValueError):
        return redirect('/ideas?err=Invalid+exit+price')

    ok, result = close_idea(idea_id, sell_price, sell_reason, sell_image)
    if ok:
        sign = '+' if result >= 0 else ''
        return redirect(f'/ideas?msg=Idea+closed.+P%26L:+{sign}${result:.2f}')
    else:
        return redirect(f'/ideas?err={result}')


@app.route('/ideas/delete/<int:idea_id>')
def ideas_delete(idea_id):
    if not is_admin():
        return redirect('/ideas')
    delete_idea(idea_id)
    return redirect('/ideas?msg=Idea+deleted')


@app.route('/ideas/image/<filename>')
def ideas_image(filename):
    return send_from_directory(UPLOADS_DIR, filename)


@app.route('/service-worker.js')
def service_worker():
    # Served from root (not /static/) so its scope covers the whole site, not just /static/.
    resp = send_from_directory(os.path.join(BASE_DIR, 'static'), 'service-worker.js')
    resp.headers['Service-Worker-Allowed'] = '/'
    return resp


@app.route('/app')
def picks_app():
    """
    Installable mobile PWA view — read-only trade ideas grouped by system
    (swing pullback / range breakout / long-term). Each idea is a fixed
    $10k hypothetical buy-in, so the P&L shown is exactly what a member's
    P&L would have been had they put $10k into that idea when it was
    posted. Posting/closing ideas stays on the desktop /ideas page.
    """
    open_ideas   = get_open_ideas()
    closed_ideas = get_closed_ideas()

    total_pnl = sum(i['pnl'] for i in open_ideas) + sum(i['pnl'] for i in closed_ideas)

    daily_changes = get_daily_changes([i['ticker'] for i in open_ideas])
    daily_pnl_total = sum(
        i['shares'] * (daily_changes[i['ticker']][0] - daily_changes[i['ticker']][1])
        for i in open_ideas if i['ticker'] in daily_changes
    )

    active_style = request.args.get('style', 'swing_pullback')
    if active_style not in STYLES:
        active_style = 'swing_pullback'

    pnl_color  = '#22c55e' if total_pnl >= 0 else '#ef4444'
    pnl_sign   = '+' if total_pnl >= 0 else ''
    dpnl_color = '#22c55e' if daily_pnl_total >= 0 else '#ef4444'
    dpnl_sign  = '+' if daily_pnl_total >= 0 else ''

    summary_html = f"""
    <div class="app-summary">
      <div><div class="app-summary-label">Total P&amp;L</div><div class="app-summary-value" style="color:{pnl_color}">{pnl_sign}${total_pnl:,.2f}</div></div>
      <div><div class="app-summary-label">Today</div><div class="app-summary-value" style="color:{dpnl_color}">{dpnl_sign}${daily_pnl_total:,.2f}</div></div>
      <div><div class="app-summary-label">Open Ideas</div><div class="app-summary-value">{len(open_ideas)}</div></div>
    </div>"""

    style_open   = [i for i in open_ideas if i['style'] == active_style]
    style_closed = [i for i in closed_ideas if i['style'] == active_style]

    if style_open:
        cards_html = ''
        for i in style_open:
            pnl_c = '#22c55e' if i['pnl'] >= 0 else '#ef4444'
            sign  = '+' if i['pnl'] >= 0 else ''
            img_html = f'<img src="/ideas/image/{i["image_path"]}" class="app-card-img">' if i['image_path'] else ''
            reason_html = f'<p class="app-card-reason">{i["reason"]}</p>' if i['reason'] else ''
            cards_html += f"""
            <div class="app-card">
              <div class="app-card-top">
                <div>
                  <a href="/chart/{i['ticker']}" class="app-card-ticker">{i['ticker']}</a>
                  <span class="app-card-date">posted {i['posted_date']}</span>
                </div>
                <span class="app-card-pnl" style="color:{pnl_c}">{sign}${i['pnl']:,.2f} ({sign}{i['pnl_pct']:.1f}%)</span>
              </div>
              {img_html}
              {reason_html}
              <div class="app-card-stats">
                <div><span>Entry</span><strong>${fmt_num(i['buy_price'])}</strong></div>
                <div><span>Current</span><strong>${fmt_num(i['current_price'])}</strong></div>
                <div><span>$10k Now Worth</span><strong>${i['value']:,.2f}</strong></div>
              </div>
            </div>"""
    else:
        cards_html = '<p class="app-empty">No open ideas in this system yet.</p>'

    closed_html = ''
    if style_closed:
        rows = ''
        for i in style_closed:
            pnl_c = '#22c55e' if i['pnl'] >= 0 else '#ef4444'
            sign  = '+' if i['pnl'] >= 0 else ''
            rows += f"""
            <div class="app-closed-row">
              <div>
                <span class="app-closed-ticker">{i['ticker']}</span>
                <span class="app-closed-date">{i['posted_date']} → {i['sell_date']}</span>
              </div>
              <span style="color:{pnl_c};font-weight:700">{sign}${i['pnl']:,.2f} ({sign}{i['pnl_pct']:.1f}%)</span>
            </div>"""
        closed_html = f'<h2 class="app-section-h">Track Record</h2><div class="app-closed-list">{rows}</div>'

    tabs_html = ''
    for key, label in STYLES.items():
        short = label.split('—')[0].strip()
        active_cls = 'active' if key == active_style else ''
        tabs_html += f'<a href="/app?style={key}" class="app-tab {active_cls}">{short}</a>'

    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<title>Jimmy Trader Ideas</title>
<link rel="manifest" href="/static/manifest.json">
<meta name="theme-color" content="#0a0c14">
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-status-bar-style" content="black-translucent">
<meta name="apple-mobile-web-app-title" content="JT Picks">
<link rel="apple-touch-icon" href="/static/icons/icon-192.png">
<style>
  * {{ box-sizing:border-box }}
  body {{ margin:0;background:#0a0c14;color:#fff;font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;padding-bottom:76px }}
  header {{ padding:16px;text-align:center;border-bottom:1px solid #1a1d2e }}
  header h1 {{ margin:0;font-size:1.1rem }}
  header p {{ margin:4px 0 0;font-size:.72rem;color:#555 }}
  .app-summary {{ display:flex;justify-content:space-around;padding:14px 8px;border-bottom:1px solid #1a1d2e }}
  .app-summary-label {{ font-size:.7rem;color:#666;text-transform:uppercase;letter-spacing:.03em }}
  .app-summary-value {{ font-size:1rem;font-weight:700;margin-top:2px }}
  .app-tabbar {{ position:fixed;bottom:0;left:0;right:0;display:flex;background:#12141f;border-top:1px solid #1a1d2e;padding:6px env(safe-area-inset-right) calc(6px + env(safe-area-inset-bottom)) env(safe-area-inset-left) }}
  .app-tab {{ flex:1;text-align:center;padding:10px 4px;color:#666;text-decoration:none;font-size:.78rem;font-weight:600;border-radius:8px }}
  .app-tab.active {{ color:#fff;background:#1f3a8a33 }}
  main {{ padding:14px }}
  .app-section-h {{ font-size:.85rem;color:#888;margin:20px 0 10px }}
  .app-card {{ background:#12141f;border:1px solid #1a1d2e;border-radius:12px;padding:14px;margin-bottom:12px }}
  .app-card-top {{ display:flex;justify-content:space-between;align-items:flex-start;gap:8px;margin-bottom:8px }}
  .app-card-ticker {{ font-size:1.15rem;font-weight:700;color:#60a5fa;text-decoration:none }}
  .app-card-date {{ display:block;font-size:.7rem;color:#555;margin-top:2px }}
  .app-card-pnl {{ font-size:1rem;font-weight:700;white-space:nowrap }}
  .app-card-img {{ width:100%;border-radius:8px;margin-bottom:10px;border:1px solid #1a1d2e }}
  .app-card-reason {{ font-size:.83rem;color:#aaa;line-height:1.5;margin:0 0 10px }}
  .app-card-stats {{ display:flex;gap:14px;font-size:.8rem }}
  .app-card-stats span {{ display:block;color:#555;font-size:.7rem }}
  .app-empty {{ text-align:center;color:#666;padding:40px 0;font-size:.9rem }}
  .app-closed-list {{ background:#12141f;border:1px solid #1a1d2e;border-radius:12px;overflow:hidden }}
  .app-closed-row {{ display:flex;justify-content:space-between;align-items:center;padding:10px 14px;font-size:.85rem;border-bottom:1px solid #1a1d2e }}
  .app-closed-row:last-child {{ border-bottom:none }}
  .app-closed-ticker {{ font-weight:700;color:#60a5fa;margin-right:8px }}
  .app-closed-date {{ font-size:.7rem;color:#555 }}
</style>
</head>
<body>
<header><h1>Jimmy Trader Ideas</h1><p>${IDEA_NOTIONAL:,.0f} per idea &middot; what your P&amp;L would have been</p></header>
{summary_html}
<main>{cards_html}{closed_html}</main>
<nav class="app-tabbar">{tabs_html}</nav>
<script>
if ('serviceWorker' in navigator) {{
  window.addEventListener('load', () => navigator.serviceWorker.register('/service-worker.js'));
}}
</script>
</body>
</html>"""


# ─── Options Picks (dummy $100k long-calls/puts paper account) ────────────────

@app.route('/options-picks')
def options_picks_page():
    positions = get_options_positions()
    history   = get_options_history()
    cash      = get_options_account()
    port_val  = get_options_portfolio_value(positions)
    total_val = cash + port_val
    total_pnl = total_val - 100_000.0

    pnl_color = '#22c55e' if total_pnl >= 0 else '#ef4444'
    pnl_sign  = '+' if total_pnl >= 0 else ''
    open_pnl  = sum(p['pnl'] for p in positions)
    open_color = '#22c55e' if open_pnl >= 0 else '#ef4444'
    open_sign  = '+' if open_pnl >= 0 else ''

    summary = f"""
    <div class="grid4" style="margin-bottom:24px">
      <div class="card">
        <div class="stat-label">Cash Available</div>
        <div class="stat-value" style="font-size:1.3rem">${cash:,.2f}</div>
        <div class="stat-sub">of $100,000 starting balance</div>
      </div>
      <div class="card">
        <div class="stat-label">Portfolio Value</div>
        <div class="stat-value" style="font-size:1.3rem">${port_val:,.2f}</div>
        <div class="stat-sub">{len(positions)} open position{'s' if len(positions)!=1 else ''}</div>
      </div>
      <div class="card">
        <div class="stat-label">Total P&amp;L</div>
        <div class="stat-value" style="font-size:1.3rem;color:{pnl_color}">{pnl_sign}${total_pnl:,.2f}</div>
        <div class="stat-sub" style="color:{pnl_color}">{pnl_sign}{total_pnl/1000:.1f}% on $100k</div>
      </div>
      <div class="card">
        <div class="stat-label">Open P&amp;L</div>
        <div class="stat-value" style="font-size:1.3rem;color:{open_color}">{open_sign}${open_pnl:,.2f}</div>
        <div class="stat-sub" style="color:{open_color}">unrealised, mark-to-model</div>
      </div>
    </div>"""

    note = """
    <p class="note" style="margin-bottom:20px">
      Dummy paper account &mdash; not real options market data. Positions are marked to market
      with Black-Scholes using the real underlying stock price and real time-to-expiry, with an
      assumed flat implied volatility set when the trade was opened. See
      <a href="/how-it-works" style="color:#60a5fa">Options 101</a> for how the pricing works.
    </p>"""

    reset_form = '' if not is_admin() else """
    <form method="POST" action="/options-picks/reset" style="margin-bottom:20px"
      onsubmit="return confirm('Reset the options account? This deletes ALL positions and trade history and restores cash to $100,000. This cannot be undone.')">
      <button type="submit" class="btn" style="background:#3a1414;color:#f87171;padding:7px 14px;font-size:.82rem">Reset Account</button>
    </form>"""

    add_form = '' if not is_admin() else """
    <section>
      <h2>Add New Options Trade</h2>
      <form method="POST" action="/options-picks/buy">
        <div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:12px;margin-bottom:12px">
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Ticker *</label>
            <input name="ticker" placeholder="e.g. AAPL" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Type *</label>
            <select name="option_type" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
              <option value="CALL">Call</option>
              <option value="PUT">Put</option>
            </select>
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Strike *</label>
            <input name="strike" type="number" step="0.01" placeholder="e.g. 150.00" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Expiry Date *</label>
            <input name="expiry_date" type="date" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Contracts *</label>
            <input name="contracts" type="number" step="1" min="1" value="1" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Entry Premium ($/share) *</label>
            <input name="entry_premium" type="number" step="0.01" placeholder="e.g. 4.50" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Assumed IV %</label>
            <input name="assumed_iv" type="number" step="1" placeholder="e.g. 40" style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
        </div>
        <div style="margin-bottom:16px">
          <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Thesis</label>
          <textarea name="reason" rows="3" placeholder="Why this trade..." style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.88rem;resize:vertical"></textarea>
        </div>
        <button type="submit" class="btn btn-green">+ Add Trade</button>
      </form>
    </section>"""

    pos_html = ''
    if positions:
        cards = ''
        for p in positions:
            pnl_c = '#22c55e' if p['pnl'] >= 0 else '#ef4444'
            sign  = '+' if p['pnl'] >= 0 else ''
            type_c = '#22c55e' if p['option_type'] == 'CALL' else '#ef4444'
            expired_badge = ' <span style="color:#f59e0b;font-size:.78rem">(expired)</span>' if p['expired'] else ''
            spot_str = f"${p['spot']:.2f}" if p['spot'] is not None else 'n/a'
            source_badge = (' <span style="color:#22c55e;font-size:.7rem;font-weight:600" title="Real market quote">● LIVE</span>'
                             if p.get('price_source') == 'real' else
                             ' <span style="color:#666;font-size:.7rem" title="Black-Scholes estimate, no real quote available">○ modeled</span>')
            reason_html = f'<p style="color:#aaa;font-size:.83rem;margin-bottom:12px;line-height:1.5">{p["reason"]}</p>' if p['reason'] else ''

            if is_admin():
                action_html = f"""
                <div style="display:flex;gap:8px;align-items:center">
                  <button class="btn btn-amber" style="padding:7px 16px"
                    onclick="openOptSellModal({p['id']},'{p['ticker']}','{p['option_type']}',{p['strike']},{p['current_premium']:.4f},'/options-picks/sell/{p['id']}')">Close</button>
                  <a href="/chart/{p['ticker']}" class="btn btn-blue" style="padding:7px 14px;font-size:.82rem">Chart</a>
                </div>"""
            else:
                action_html = f'<a href="/chart/{p["ticker"]}" class="btn btn-blue" style="padding:7px 14px;font-size:.82rem">View Chart</a>'

            cards += f"""
            <div class="card" style="margin-bottom:16px">
              <div style="display:flex;justify-content:space-between;align-items:flex-start;flex-wrap:wrap;gap:8px;margin-bottom:8px">
                <div>
                  <a href="/chart/{p['ticker']}" style="font-size:1.3rem;font-weight:700;color:#60a5fa">{p['ticker']}</a>
                  <span style="color:{type_c};font-weight:700;margin-left:8px">${fmt_num(p['strike'])} {p['option_type']}</span>
                  <span style="color:#555;font-size:.78rem;margin-left:10px">opened {p['bought_date']}</span>{expired_badge}
                </div>
                <span style="font-size:1.1rem;font-weight:700;color:{pnl_c}">{sign}${p['pnl']:,.2f} ({sign}{p['pnl_pct']:.1f}%)</span>
              </div>
              {reason_html}
              <div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(130px,1fr));gap:8px;margin-bottom:14px;font-size:.83rem">
                <div><span style="color:#555">Contracts</span><br><strong>{p['contracts']}</strong></div>
                <div><span style="color:#555">Underlying</span><br><strong>{spot_str}</strong></div>
                <div><span style="color:#555">Days to Exp</span><br><strong>{p['dte']}</strong></div>
                <div><span style="color:#555">Entry Premium</span><br><strong>${fmt_num(p['entry_premium'])}</strong></div>
                <div><span style="color:#555">Current Premium</span><br><strong>${fmt_num(p['current_premium'])}</strong>{source_badge}</div>
                <div><span style="color:#555">Cost Basis</span><br><strong>${p['cost']:,.2f}</strong></div>
                <div><span style="color:#555">Market Value</span><br><strong>${p['value']:,.2f}</strong></div>
                <div><span style="color:#555">Expiry</span><br><strong>{p['expiry_date']}</strong></div>
              </div>
              {action_html}
            </div>"""
        pos_html = f'<section><h2>Open Positions ({len(positions)})</h2>{cards}</section>'
    else:
        pos_html = '<section><h2>Open Positions</h2><p class="note">No open options trades yet.</p></section>'

    hist_html = ''
    if history:
        rows = ''
        for t in history:
            action_color = '#22c55e' if t['action'] == 'BUY' else '#ef4444'
            type_c = '#22c55e' if t['option_type'] == 'CALL' else '#ef4444'
            pnl_str = ''
            if t['pnl'] is not None:
                pc = '#22c55e' if t['pnl'] >= 0 else '#ef4444'
                pnl_str = f'<span style="color:{pc}">{("+" if t["pnl"]>=0 else "")}${t["pnl"]:,.2f}</span>'
            rows += f"""<tr>
              <td>{t['trade_date']}</td>
              <td><strong style="color:#60a5fa">{t['ticker']}</strong></td>
              <td><span style="color:{type_c}">${fmt_num(t['strike'])} {t['option_type']}</span></td>
              <td>{t['expiry_date']}</td>
              <td><span style="color:{action_color};font-weight:700">{t['action']}</span></td>
              <td>{t['contracts']}</td>
              <td>${fmt_num(t['premium'])}</td>
              <td>${t['total']:,.2f}</td>
              <td>{pnl_str}</td>
            </tr>"""
        hist_html = f"""
        <section>
          <h2>Trade History</h2>
          <style>
            table{{width:100%;border-collapse:collapse;font-size:.82rem}}
            th{{text-align:left;padding:8px 10px;color:#555;border-bottom:1px solid #2a2d3e;font-weight:500}}
            td{{padding:8px 10px;border-bottom:1px solid #151820;white-space:nowrap}}
            tr:hover td{{background:#1f2235}}
          </style>
          <div style="overflow-x:auto">
          <table>
            <tr><th>Date</th><th>Ticker</th><th>Contract</th><th>Expiry</th><th>Action</th><th>Contracts</th><th>Premium</th><th>Total</th><th>P&amp;L</th></tr>
            {rows}
          </table>
          </div>
        </section>"""

    msg = request.args.get('msg', '')
    msg_html = f'<div style="background:#1a2e1a;border:1px solid #22c55e;border-radius:8px;padding:12px 16px;margin-bottom:20px;color:#86efac">{msg}</div>' if msg else ''
    err = request.args.get('err', '')
    err_html = f'<div class="err-box">{err}</div>' if err else ''

    sell_modal = """
    <div id="opt-sell-modal" style="display:none;position:fixed;inset:0;background:rgba(0,0,0,.75);z-index:9000;align-items:center;justify-content:center">
      <div style="background:#13151f;border:1px solid #2a2d3e;border-radius:12px;padding:28px;width:100%;max-width:500px;margin:20px">
        <h3 id="opt-sell-modal-title" style="margin:0 0 20px">Close Position</h3>
        <form id="opt-sell-form" method="POST">
          <div style="margin-bottom:14px">
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Exit Premium ($/share) *</label>
            <input id="opt-sell-price-input" name="sell_premium" type="number" step="0.01" required
              style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div style="margin-bottom:20px">
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Notes</label>
            <textarea name="sell_reason" rows="3" placeholder="Took profit, thesis broke, expired worthless..."
              style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.88rem;resize:vertical"></textarea>
          </div>
          <div style="display:flex;gap:10px">
            <button type="submit" class="btn btn-amber" style="flex:1">Confirm Close</button>
            <button type="button" class="btn" style="flex:1;background:#252839" onclick="closeOptSellModal()">Cancel</button>
          </div>
        </form>
      </div>
    </div>
    <script>
    function openOptSellModal(pickId, ticker, optType, strike, currentPremium, action) {
      document.getElementById('opt-sell-modal-title').textContent = 'Close ' + ticker + ' $' + strike + ' ' + optType;
      document.getElementById('opt-sell-price-input').value = currentPremium.toFixed(2);
      document.getElementById('opt-sell-form').action = action;
      document.getElementById('opt-sell-modal').style.display = 'flex';
    }
    function closeOptSellModal() {
      document.getElementById('opt-sell-modal').style.display = 'none';
    }
    document.addEventListener('keydown', function(e) {
      if (e.key === 'Escape') closeOptSellModal();
    });
    </script>"""

    content = err_html + msg_html + summary + note + reset_form + add_form + pos_html + hist_html + sell_modal
    return page_wrap('Options Picks', 'optionspicks', content)


@app.route('/options-picks/buy', methods=['POST'])
def options_picks_buy():
    if not is_admin():
        return redirect('/options-picks')

    ticker        = request.form.get('ticker', '').strip().upper()
    option_type   = request.form.get('option_type', 'CALL').strip().upper()
    strike        = request.form.get('strike', 0)
    expiry_date   = request.form.get('expiry_date', '').strip()
    contracts     = request.form.get('contracts', 1)
    entry_premium = request.form.get('entry_premium', 0)
    reason        = request.form.get('reason', '').strip()
    iv_input      = request.form.get('assumed_iv', '').strip()

    try:
        strike_val = float(strike)
        assumed_iv = float(iv_input) / 100.0 if iv_input else None  # None = derive from spot price
        ok, result = buy_option(ticker, option_type, strike_val, expiry_date,
                                 contracts, entry_premium, assumed_iv, reason)
    except (ValueError, TypeError) as e:
        ok, result = False, f"Invalid input: {e}"

    if ok:
        return redirect(f'/options-picks?msg=Opened+{contracts}x+{ticker}+${strike}+{option_type}')
    else:
        return redirect(f'/options-picks?err={result}')


@app.route('/options-picks/sell/<int:pick_id>', methods=['POST'])
def options_picks_sell(pick_id):
    if not is_admin():
        return redirect('/options-picks')

    sell_premium = request.form.get('sell_premium', 0)
    sell_reason  = request.form.get('sell_reason', '').strip()

    ok, result = sell_option(pick_id, sell_premium, sell_reason)
    if ok:
        sign = '+' if result >= 0 else ''
        return redirect(f'/options-picks?msg=Position+closed.+P%26L:+{sign}${result:.2f}')
    else:
        return redirect(f'/options-picks?err={result}')


@app.route('/options-picks/reset', methods=['POST'])
def options_picks_reset():
    if not is_admin():
        return redirect('/options-picks')

    ok, err = reset_options_account()
    if ok:
        return redirect('/options-picks?msg=Account+reset+to+%24100%2C000')
    else:
        return redirect(f'/options-picks?err={err}')


# ─── Options Tracker (cheapest OTM put/call, day-by-day to expiry) ────────────

def _tracker_table_html(tracker):
    rows = build_tracker_rows(tracker)
    row_html = ''
    for r in rows:
        hl = 'background:#3a2a10' if r['is_today'] else ''
        close_str = f"${r['close']:.2f}" if r['close'] is not None else '—'
        put_str   = f"${r['put_price']:.2f}"  if r['put_price']  is not None else '—'
        call_str  = f"${r['call_price']:.2f}" if r['call_price'] is not None else '—'
        if r.get('put_real'):
            put_str += ' ●'
        if r.get('call_real'):
            call_str += ' ●'
        row_html += f"""<tr style="{hl}">
          <td style="color:#aaa">{r['date']}</td>
          <td style="background:#1f1320;color:#f9a8d4">${fmt_num(tracker['put_strike'])}</td>
          <td style="background:#1f1320;color:#f9a8d4;font-weight:600">{put_str}</td>
          <td style="background:#000;color:#fff;font-weight:700">{close_str}</td>
          <td style="background:#0d1f14;color:#4ade80">${fmt_num(tracker['call_strike'])}</td>
          <td style="background:#0d1f14;color:#4ade80;font-weight:600">{call_str}</td>
        </tr>"""

    del_btn = ''
    if is_admin():
        del_btn = f"""
        <form method="POST" action="/options-tracker/delete/{tracker['id']}" style="display:inline"
          onsubmit="return confirm('Delete this tracker?')">
          <button type="submit" class="btn" style="background:#3a1414;color:#f87171;padding:5px 12px;font-size:.78rem">Delete</button>
        </form>"""

    return f"""
    <div class="card" style="margin-bottom:24px">
      <div style="display:flex;justify-content:space-between;align-items:center;flex-wrap:wrap;gap:8px;margin-bottom:12px">
        <div>
          <span style="font-size:1.15rem;font-weight:700;color:#60a5fa">{tracker['ticker']}</span>
          <span style="color:#555;font-size:.82rem;margin-left:10px">
            opened {tracker['created_date']} &middot; expires {tracker['expiry_date']} &middot; {(tracker['assumed_iv']*100):.0f}% assumed IV
          </span>
        </div>
        {del_btn}
      </div>
      <div style="overflow-x:auto">
      <table style="width:100%;border-collapse:collapse;font-size:.85rem;min-width:560px">
        <tr>
          <th style="padding:8px 10px;border-bottom:1px solid #2a2d3e"></th>
          <th colspan="2" style="background:#3b0f2e;color:#f9a8d4;padding:8px 10px;text-align:center">Put Option</th>
          <th style="background:#000;color:#fff;padding:8px 10px;text-align:center">{tracker['ticker']} Close</th>
          <th colspan="2" style="background:#062e17;color:#4ade80;padding:8px 10px;text-align:center">Call Option</th>
        </tr>
        <tr>
          <th style="padding:6px 10px;color:#555;font-weight:500;text-align:left">Date</th>
          <th style="padding:6px 10px;color:#f9a8d4;font-weight:500">Strike</th>
          <th style="padding:6px 10px;color:#f9a8d4;font-weight:500">Price</th>
          <th style="padding:6px 10px;color:#888;font-weight:500"></th>
          <th style="padding:6px 10px;color:#4ade80;font-weight:500">Strike</th>
          <th style="padding:6px 10px;color:#4ade80;font-weight:500">Price</th>
        </tr>
        {row_html}
      </table>
      </div>
    </div>"""


@app.route('/options-tracker')
def options_tracker_page():
    trackers = get_trackers()

    note = """
    <p class="note" style="margin-bottom:20px">
      Tracks the cheapest deep out-of-the-money put and call for a chosen ticker/expiry, day by
      day. Prices marked <strong style="color:#4ade80">●</strong> are real market quotes (US-listed
      tickers only, pulled when prices refresh); everything else is a Black-Scholes estimate against
      the real closing price. See <a href="/how-it-works" style="color:#60a5fa">Options 101</a>
      for how the modeled pricing works.
    </p>"""

    add_form = '' if not is_admin() else """
    <section>
      <h2>New Tracker</h2>
      <form method="POST" action="/options-tracker/create">
        <div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(160px,1fr));gap:12px;margin-bottom:12px">
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Ticker *</label>
            <input name="ticker" placeholder="e.g. NFLX" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Expiry Date *</label>
            <input name="expiry_date" type="date" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
        </div>
        <button type="submit" class="btn btn-green">+ Create Tracker</button>
      </form>
    </section>"""

    msg = request.args.get('msg', '')
    msg_html = f'<div style="background:#1a2e1a;border:1px solid #22c55e;border-radius:8px;padding:12px 16px;margin-bottom:20px;color:#86efac">{msg}</div>' if msg else ''
    err = request.args.get('err', '')
    err_html = f'<div class="err-box">{err}</div>' if err else ''

    tables_html = ''.join(_tracker_table_html(t) for t in trackers) if trackers else \
        '<p class="note">No trackers yet.</p>'

    content = err_html + msg_html + note + add_form + f'<section><h2>Trackers</h2>{tables_html}</section>'
    return page_wrap('Options Tracker', 'optionstracker', content)


@app.route('/options-tracker/create', methods=['POST'])
def options_tracker_create():
    if not is_admin():
        return redirect('/options-tracker')

    ticker      = request.form.get('ticker', '').strip()
    expiry_date = request.form.get('expiry_date', '').strip()

    ok, result = create_tracker(ticker, expiry_date)
    if ok:
        return redirect(f'/options-tracker?msg=Tracker+created+for+{ticker.upper()}')
    else:
        return redirect(f'/options-tracker?err={result}')


@app.route('/options-tracker/delete/<int:tracker_id>', methods=['POST'])
def options_tracker_delete(tracker_id):
    if not is_admin():
        return redirect('/options-tracker')
    delete_tracker(tracker_id)
    return redirect('/options-tracker?msg=Tracker+deleted')


# ─── Ask Jimmy ────────────────────────────────────────────────────────────────

def ask_auth_form(mode='login'):
    """Shared login/register form HTML."""
    other = 'register' if mode == 'login' else 'login'
    other_label = "Don't have an account? Register" if mode == 'login' else 'Already have an account? Login'
    extra = '<input name="email" type="email" placeholder="Email (optional)" style="width:100%;padding:9px 12px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem;margin-bottom:10px">' if mode == 'register' else ''
    return f"""
    <div style="max-width:380px;margin:60px auto">
      <section>
        <h2>{'Create Account' if mode == 'register' else 'Login to Ask Jimmy'}</h2>
        <form method="POST" style="margin-top:4px">
          <input name="username" placeholder="Username" required autofocus
            style="width:100%;padding:9px 12px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem;margin-bottom:10px">
          {extra}
          <input name="password" type="password" placeholder="Password" required
            style="width:100%;padding:9px 12px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem;margin-bottom:14px">
          <button type="submit" class="btn btn-blue" style="width:100%;margin-bottom:12px">
            {'Create Account' if mode == 'register' else 'Login'}
          </button>
          <a href="/ask/{other}" style="font-size:.8rem;color:#555">{other_label}</a>
        </form>
      </section>
    </div>"""


@app.route('/ask')
def ask_page():
    uid   = current_user_id()
    admin = is_admin()
    questions = get_questions(user_id=uid, admin=admin)

    msg = request.args.get('msg', '')
    err = request.args.get('err', '')
    msg_html = f'<div style="background:#1a2e1a;border:1px solid #22c55e;border-radius:8px;padding:12px 16px;margin-bottom:20px;color:#86efac">{msg}</div>' if msg else ''
    err_html = f'<div class="err-box">{err}</div>' if err else ''

    # Submit form
    if uid or admin:
        submit_section = f"""
        <section>
          <h2>Ask Jimmy to Analyse a Stock</h2>
          <form method="POST" action="/ask/submit">
            <div style="display:flex;gap:10px;margin-bottom:10px;flex-wrap:wrap">
              <input name="ticker" placeholder="Ticker (e.g. AAPL)" required
                style="width:160px;padding:9px 12px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem"
                oninput="this.value=this.value.toUpperCase()" id="tickerInput">
              <button type="button" class="btn btn-blue" onclick="previewChart()" style="padding:9px 16px">Preview Chart</button>
            </div>
            <div id="chart-preview" style="display:none;margin-bottom:12px">
              <div id="preview-box" style="width:100%;height:300px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px"></div>
            </div>
            <textarea name="question" rows="3" required placeholder="What would you like Jimmy to analyse? (e.g. Is this in a channel? Good entry point?)"
              style="width:100%;padding:9px 12px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem;resize:vertical;margin-bottom:12px"></textarea>
            <button type="submit" class="btn btn-green">Submit Question</button>
          </form>
        </section>
        <script src="https://unpkg.com/lightweight-charts@4.1.3/dist/lightweight-charts.standalone.production.js"></script>
        <script>
        let previewChart_ = null;
        function previewChart() {{
          const ticker = document.getElementById('tickerInput').value.trim();
          if (!ticker) return;
          const box = document.getElementById('chart-preview');
          box.style.display = 'block';
          const el = document.getElementById('preview-box');
          el.innerHTML = '<p style="color:#555;padding:20px;font-size:.85rem">Loading ' + ticker + '...</p>';
          if (previewChart_) {{ previewChart_.remove(); previewChart_ = null; }}
          fetch('/api/chart-data/' + ticker)
            .then(r => r.json())
            .then(data => {{
              if (data.error) {{ el.innerHTML = '<p style="color:#f87171;padding:20px">' + data.error + '</p>'; return; }}
              el.innerHTML = '';
              previewChart_ = LightweightCharts.createChart(el, {{
                layout: {{ background: {{ color: '#0a0c14' }}, textColor: '#888' }},
                grid: {{ vertLines: {{ color: '#1a1d2e' }}, horzLines: {{ color: '#1a1d2e' }} }},
                rightPriceScale: {{ borderColor: '#2a2d3e' }},
                timeScale: {{ borderColor: '#2a2d3e' }},
                height: 300,
              }});
              const c = previewChart_.addCandlestickSeries({{
                upColor:'#22c55e',downColor:'#ef4444',
                borderUpColor:'#22c55e',borderDownColor:'#ef4444',
                wickUpColor:'#22c55e',wickDownColor:'#ef4444'
              }});
              c.setData(data.ohlcv);
              const e5  = previewChart_.addLineSeries({{color:'#60a5fa',lineWidth:1}});
              const e26 = previewChart_.addLineSeries({{color:'#f59e0b',lineWidth:1}});
              e5.setData(data.ema5); e26.setData(data.ema26);
              previewChart_.timeScale().fitContent();
            }});
        }}
        </script>"""
    else:
        submit_section = f"""
        <section style="text-align:center;padding:32px">
          <p style="color:#aaa;margin-bottom:16px">Login or create a free account to ask Jimmy to analyse a stock.</p>
          <div style="display:flex;gap:10px;justify-content:center">
            <a href="/ask/login"    class="btn btn-blue">Login</a>
            <a href="/ask/register" class="btn btn-green">Create Account</a>
          </div>
        </section>"""

    # Q&A list
    qa_html = ''
    if questions:
        for q in questions:
            is_pending = q['status'] == 'pending'
            ticker_link = f'<a href="/chart/{q["ticker"]}" style="font-size:1.1rem;font-weight:700;color:#60a5fa">{q["ticker"]}</a>'

            answer_block = ''
            if q['answer']:
                answer_block = f"""
                <div style="background:#0f1f0f;border-left:3px solid #22c55e;border-radius:0 6px 6px 0;padding:14px 16px;margin-top:12px">
                  <div style="font-size:.72rem;color:#22c55e;font-weight:700;margin-bottom:6px">JIMMY'S ANALYSIS · {q['answered_date']}</div>
                  <p style="color:#d1fae5;font-size:.9rem;line-height:1.6;white-space:pre-wrap">{q['answer']}</p>
                </div>"""
            elif is_pending:
                answer_block = "<div style=\"color:#555;font-size:.82rem;margin-top:10px;font-style:italic\">⏳ Awaiting Jimmy's analysis...</div>"

            # Admin answer form
            admin_form = ''
            if admin and is_pending:
                admin_form = f"""
                <form method="POST" action="/ask/answer/{q['id']}" style="margin-top:12px">
                  <textarea name="answer" rows="4" placeholder="Type your analysis here..." required
                    style="width:100%;padding:9px 12px;background:#0a0c14;border:1px solid #22c55e;border-radius:6px;color:#fff;font-size:.88rem;resize:vertical;margin-bottom:8px"></textarea>
                  <button type="submit" class="btn btn-green" style="padding:7px 16px;font-size:.82rem">Post Analysis</button>
                </form>"""

            pending_badge = '<span style="background:#2a1f00;color:#f59e0b;font-size:.7rem;padding:2px 8px;border-radius:10px;margin-left:8px">PENDING</span>' if is_pending else ''

            qa_html += f"""
            <div class="card" style="margin-bottom:16px">
              <div style="display:flex;align-items:center;gap:10px;margin-bottom:10px;flex-wrap:wrap">
                {ticker_link}
                {pending_badge}
                <span style="color:#555;font-size:.75rem;margin-left:auto">asked by <strong style="color:#888">{q['username']}</strong> · {q['created_date']}</span>
              </div>
              <p style="color:#ccc;font-size:.9rem;line-height:1.5;white-space:pre-wrap">{q['question']}</p>
              {answer_block}
              {admin_form}
            </div>"""
    else:
        qa_html = '<div class="card" style="text-align:center;padding:32px;color:#555">No questions yet. Be the first to ask!</div>'

    content = f"""
    {err_html}{msg_html}
    {submit_section}
    <section>
      <h2>{('All Questions' if admin else "Jimmy's Stock Analyses")}</h2>
      {qa_html}
    </section>"""

    return page_wrap("Ask Jimmy", 'ask', content)


@app.route('/ask/submit', methods=['POST'])
def ask_submit():
    uid   = current_user_id()
    uname = current_username()
    if not uid:
        return redirect('/ask/login')
    ticker   = request.form.get('ticker', '').strip().upper()
    question = request.form.get('question', '').strip()
    ok, result = submit_question(uid, uname, ticker, question)
    if ok:
        return redirect('/ask?msg=Question+submitted!+Jimmy+will+analyse+it+soon.')
    return redirect(f'/ask?err={result}')


@app.route('/ask/answer/<int:qid>', methods=['POST'])
def ask_answer(qid):
    if not is_admin():
        return redirect('/ask')
    answer = request.form.get('answer', '').strip()
    if answer:
        answer_question(qid, answer)
    return redirect('/ask?msg=Analysis+posted!')


@app.route('/ask/register', methods=['GET', 'POST'])
def ask_register():
    if request.method == 'POST':
        username = request.form.get('username', '').strip()
        email    = request.form.get('email', '').strip()
        password = request.form.get('password', '')
        ok, result = register_user(username, email, password)
        if ok:
            session['user_id']  = result
            session['username'] = username
            return redirect('/ask?msg=Welcome+' + username + '!')
        return page_wrap('Register', 'ask', ask_auth_form('register') +
                         f'<p style="color:#f87171;text-align:center;margin-top:-16px;font-size:.85rem">{result}</p>')
    return page_wrap('Register', 'ask', ask_auth_form('register'))


@app.route('/ask/login', methods=['GET', 'POST'])
def ask_login():
    if request.method == 'POST':
        username = request.form.get('username', '').strip()
        password = request.form.get('password', '')
        ok, result = login_user(username, password)
        if ok:
            session['user_id']  = result
            session['username'] = username
            return redirect('/ask')
        return page_wrap('Login', 'ask', ask_auth_form('login') +
                         f'<p style="color:#f87171;text-align:center;margin-top:-16px;font-size:.85rem">{result}</p>')
    return page_wrap('Login', 'ask', ask_auth_form('login'))


@app.route('/ask/logout')
def ask_logout():
    session.pop('user_id', None)
    session.pop('username', None)
    return redirect('/ask')


# ─── Range Level Scanner ──────────────────────────────────────────────────────

@app.route('/range')
def range_page():
    data = load_range_results()
    with _job_lock:
        running = _job_running
        jname = _job_name

    if is_admin():
        if running and jname == 'Range Scan':
            run_btn = '<span class="btn btn-off">Scanning...</span>'
        elif running:
            run_btn = '<span class="btn btn-off">Another job running</span>'
        else:
            run_btn = '<a href="/range/run" class="btn btn-green">▶ Run Range Scan</a>'
    else:
        run_btn = ''

    if not data:
        content = f"""
        <section>
          <h2>Range Level Scanner</h2>
          <p style="color:#aaa;margin-bottom:16px;font-size:.9rem">
            Finds stocks at 25% and 75% of their price range — natural settling zones
            with built-in 1:2 R:R.<br>
            <strong style="color:#fff">WITHIN_RANGE</strong> = enter at 25%, target 75%.
            <strong style="color:#fff">RANGE_CHANGE</strong> = enter at 75%, target next 25%.
          </p>
          <div class="btn-row">{run_btn}</div>
          <p class="note" style="margin-top:12px">No scan results yet. Run the scanner to see setups.</p>
        </section>"""
        return page_wrap('Range Levels', 'range', content, auto_refresh=(running and jname == 'Range Scan'))

    results = data['results']
    within = [r for r in results if r['trade_type'] == 'WITHIN_RANGE']
    change = [r for r in results if r['trade_type'] == 'RANGE_CHANGE']

    def build_rows(items):
        html = ''
        for r in items:
            svg = sparkline_svg(r.get('sparkline', []))
            type_color = '#22c55e' if r['trade_type'] == 'WITHIN_RANGE' else '#a78bfa'
            zone_label = '25% Zone' if r['zone'] == 'NEAR_25' else '75% Zone'
            score_color = '#22c55e' if r['quality_score'] >= 60 else ('#f59e0b' if r['quality_score'] >= 40 else '#ef4444')
            fader_color = '#22c55e' if r['fader_color'] == 'green' else ('#ef4444' if r['fader_color'] == 'red' else '#555')
            efi_color = '#22c55e' if r['efi_color'] in ('lime','green') else '#555'
            levels_json = json.dumps({
                'entry': r['entry_level'], 'stop': r['stop_level'],
                'target': r['target_level'],
                'L0': r['L0'], 'L25': r['L25'], 'L50': r['L50'],
                'L75': r['L75'], 'L100': r['L100']
            }).replace('"', '&quot;')
            html += f"""<tr class="range-row" data-ticker="{r['ticker']}" data-levels="{levels_json}"
                         style="cursor:pointer">
              <td>
                <div style="display:flex;align-items:center;gap:10px">
                  <strong style="color:#60a5fa;font-size:.95rem;min-width:52px">{r['ticker']}</strong>
                  {svg}
                </div>
              </td>
              <td style="font-weight:700">${r['price']:.2f}</td>
              <td><span style="color:{type_color};font-size:.78rem;font-weight:600">{r['trade_type'].replace('_',' ')}</span></td>
              <td style="color:#aaa;font-size:.82rem">{zone_label}</td>
              <td style="color:#22c55e">${r['entry_level']:.2f}</td>
              <td style="color:#ef4444">${r['stop_level']:.2f}</td>
              <td style="color:#60a5fa">${r['target_level']:.2f}</td>
              <td style="font-weight:600">{r['rr_ratio']:.1f}x</td>
              <td><span style="color:{fader_color};font-size:.8rem">{'●' if r['fader_color']=='green' else ('●' if r['fader_color']=='red' else '○')} {r['fader_color'].title()}</span></td>
              <td><span style="color:{efi_color};font-size:.8rem">{r['efi_color'].title()}</span></td>
              <td><span style="color:{score_color};font-weight:700">{r['quality_score']}</span></td>
            </tr>"""
        return html

    table_style = """
    <style>
    .rtable { width:100%; border-collapse:collapse; font-size:.84rem; }
    .rtable th { text-align:left; padding:8px 12px; color:#555; border-bottom:1px solid #2a2d3e;
                 font-weight:500; white-space:nowrap; cursor:pointer; user-select:none; }
    .rtable th:hover { color:#aaa; }
    .rtable th.sort-asc::after  { content:' ▲'; font-size:.6rem; color:#60a5fa; }
    .rtable th.sort-desc::after { content:' ▼'; font-size:.6rem; color:#60a5fa; }
    .rtable td { padding:8px 12px; border-bottom:1px solid #151820; vertical-align:middle; }
    .rtable .range-row:hover td { background:#1f2235; }
    .rtable .range-row.active td { background:#1a2235; }
    .chart-drop td { padding:0 !important; }
    </style>"""

    chart_js = """
    <script src="https://unpkg.com/lightweight-charts@4.1.3/dist/lightweight-charts.standalone.production.js"></script>
    <script>
    const openCharts = {};
    document.querySelectorAll('.range-row').forEach(row => {
      row.addEventListener('click', () => {
        const ticker = row.dataset.ticker;
        const levels = JSON.parse(row.dataset.levels.replace(/&quot;/g, '"'));
        const existId = 'cdrop-' + ticker;
        const exist = document.getElementById(existId);

        // Close if already open
        if (exist) {
          exist.remove();
          row.classList.remove('active');
          if (openCharts[ticker]) { openCharts[ticker].remove(); delete openCharts[ticker]; }
          return;
        }

        // Close any other open chart
        document.querySelectorAll('.chart-drop').forEach(d => d.remove());
        document.querySelectorAll('.range-row.active').forEach(r => r.classList.remove('active'));
        row.classList.add('active');

        // Insert drop row
        const drop = document.createElement('tr');
        drop.id = existId;
        drop.className = 'chart-drop';
        drop.innerHTML = `<td colspan="11" style="background:#080a10;padding:16px 20px">
          <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:10px">
            <span style="color:#fff;font-weight:700;font-size:1rem">${ticker}</span>
            <span style="color:#555;font-size:.75rem" id="cstatus-${ticker}">Loading chart...</span>
          </div>
          <div id="cmain-${ticker}" style="height:360px;background:#0a0c14;border-radius:6px"></div>
          <div id="cvol-${ticker}" style="height:70px;background:#0a0c14;border-radius:6px;margin-top:3px"></div>
          <div style="display:flex;gap:20px;flex-wrap:wrap;margin-top:10px;font-size:.78rem">
            <span style="color:#22c55e">━ Entry $${levels.entry.toFixed(2)}</span>
            <span style="color:#ef4444">╌ Stop $${levels.stop.toFixed(2)}</span>
            <span style="color:#60a5fa">╌ Target $${levels.target.toFixed(2)}</span>
            <span style="color:#555">┄ 25% $${levels.L25.toFixed(2)} &nbsp;|&nbsp; 75% $${levels.L75.toFixed(2)}</span>
          </div>
        </td>`;
        row.parentNode.insertBefore(drop, row.nextSibling);

        fetch('/api/chart-data/' + ticker)
          .then(r => r.json())
          .then(data => {
            if (data.error) {
              document.getElementById('cstatus-' + ticker).textContent = 'Error: ' + data.error;
              return;
            }
            document.getElementById('cstatus-' + ticker).textContent =
              data.bars + ' bars · ' + data.date_range;

            const chart = LightweightCharts.createChart(
              document.getElementById('cmain-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: true },
              crosshair: { mode: LightweightCharts.CrosshairMode.Normal },
            });

            const candles = chart.addCandlestickSeries({
              upColor: '#22c55e', downColor: '#ef4444',
              borderUpColor: '#22c55e', borderDownColor: '#ef4444',
              wickUpColor: '#22c55e', wickDownColor: '#ef4444',
            });
            candles.setData(data.ohlcv);

            // Price level lines
            candles.createPriceLine({ price: levels.entry,  color: '#22c55e', lineWidth: 2, lineStyle: 0, axisLabelVisible: true, title: 'Entry' });
            candles.createPriceLine({ price: levels.stop,   color: '#ef4444', lineWidth: 1, lineStyle: 2, axisLabelVisible: true, title: 'Stop' });
            candles.createPriceLine({ price: levels.target, color: '#60a5fa', lineWidth: 1, lineStyle: 2, axisLabelVisible: true, title: 'Target' });
            candles.createPriceLine({ price: levels.L25,    color: '#374151', lineWidth: 1, lineStyle: 1, axisLabelVisible: false, title: '25%' });
            candles.createPriceLine({ price: levels.L75,    color: '#374151', lineWidth: 1, lineStyle: 1, axisLabelVisible: false, title: '75%' });
            candles.createPriceLine({ price: levels.L50,    color: '#1f2937', lineWidth: 1, lineStyle: 1, axisLabelVisible: false, title: '50%' });

            const ema5  = chart.addLineSeries({ color: '#60a5fa', lineWidth: 1, title: 'EMA5' });
            const ema26 = chart.addLineSeries({ color: '#f59e0b', lineWidth: 1, title: 'EMA26' });
            ema5.setData(data.ema5);
            ema26.setData(data.ema26);
            chart.timeScale().fitContent();

            const volChart = LightweightCharts.createChart(
              document.getElementById('cvol-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: false },
            });
            const volS = volChart.addHistogramSeries({ priceFormat: { type: 'volume' }, priceScaleId: '' });
            volS.priceScale().applyOptions({ scaleMargins: { top: 0.1, bottom: 0 } });
            volS.setData(data.volume);
            volChart.timeScale().fitContent();

            chart.timeScale().subscribeVisibleLogicalRangeChange(r => volChart.timeScale().setVisibleLogicalRange(r));
            volChart.timeScale().subscribeVisibleLogicalRangeChange(r => chart.timeScale().setVisibleLogicalRange(r));

            openCharts[ticker] = chart;
          })
          .catch(e => { document.getElementById('cstatus-' + ticker).textContent = 'Failed: ' + e; });
      });
    });

    function sortRange(th) {
      const tbody = th.closest('table').querySelector('tbody');
      const idx = th.cellIndex;
      const asc = th.classList.contains('sort-desc');
      th.closest('thead').querySelectorAll('th').forEach(h => h.classList.remove('sort-asc','sort-desc'));
      th.classList.add(asc ? 'sort-asc' : 'sort-desc');
      const rows = Array.from(tbody.querySelectorAll('.range-row'));
      rows.sort((a, b) => {
        const av = a.cells[idx].textContent.trim();
        const bv = b.cells[idx].textContent.trim();
        const an = parseFloat(av.replace(/[^0-9.-]/g,'')), bn = parseFloat(bv.replace(/[^0-9.-]/g,''));
        const cmp = isNaN(an) ? av.localeCompare(bv) : an - bn;
        return asc ? cmp : -cmp;
      });
      rows.forEach(r => tbody.appendChild(r));
    }
    </script>"""

    def section_table(title, items, color):
        if not items:
            return ''
        rows = build_rows(items)
        return f"""
        <section style="margin-bottom:20px">
          <h2 style="color:{color}">{title} <span style="color:#555;font-size:.75rem;font-weight:400;text-transform:none;letter-spacing:0">({len(items)} setups) — click a row to expand chart</span></h2>
          {table_style}
          <table class="rtable">
            <thead><tr>
              <th onclick="sortRange(this)">Ticker</th><th onclick="sortRange(this)">Price</th><th onclick="sortRange(this)">Type</th><th onclick="sortRange(this)">Zone</th>
              <th onclick="sortRange(this)">Entry</th><th onclick="sortRange(this)">Stop</th><th onclick="sortRange(this)">Target</th><th onclick="sortRange(this)">R:R</th>
              <th onclick="sortRange(this)">Fader</th><th onclick="sortRange(this)">EFI</th><th onclick="sortRange(this)">Score</th>
            </tr></thead>
            <tbody>{rows}</tbody>
          </table>
        </section>"""

    log_section = ''
    if running and jname == 'Range Scan':
        log_section = f'<section><h2>Live Log</h2><pre>{get_log().replace("<","&lt;")}</pre></section>'

    content = f"""
    <section style="margin-bottom:20px">
      <h2>Range Level Scanner</h2>
      <p style="color:#aaa;margin-bottom:14px;font-size:.88rem">
        Stocks at 25%/75% of their price range — natural settling zones with built-in 1:2 R:R.<br>
        Scan date: <strong style="color:#fff">{data['scan_date']}</strong> &nbsp;·&nbsp;
        {len(results)} total setups &nbsp;·&nbsp;
        {len(within)} WITHIN_RANGE &nbsp;·&nbsp; {len(change)} RANGE_CHANGE
      </p>
      <div class="btn-row">{run_btn}</div>
    </section>
    {log_section}
    {section_table('WITHIN RANGE — Enter 25%, Target 75%', within, '#22c55e')}
    {section_table('RANGE CHANGE — Enter 75%, Target next 25%', change, '#a78bfa')}
    {chart_js}"""

    return page_wrap('Range Levels', 'range', content, auto_refresh=(running and jname == 'Range Scan'))


@app.route('/range/run')
def range_run():
    if not is_admin():
        return redirect('/range')
    start_range_scan_job()
    return redirect('/range')


# ─── ASX 200 ──────────────────────────────────────────────────────────────────

@app.route('/asx')
def asx_page():
    with _job_lock:
        running = _job_running
        jname   = _job_name

    if is_admin():
        if running and jname == 'ASX Download':
            dl_btn = '<span class="btn btn-off">Downloading...</span>'
        elif running:
            dl_btn = '<span class="btn btn-off">Another job running</span>'
        else:
            dl_btn = '<a href="/asx/download" class="btn btn-blue">↓ Download / Update ASX Data</a>'
    else:
        dl_btn = ''

    has_data = bool(get_tickers_with_data())
    if not has_data:
        content = f"""
        <section>
          <h2>ASX 200</h2>
          <p style="color:#aaa;margin-bottom:16px;font-size:.9rem">
            No ASX data in the database yet. Download it first (takes ~5 min).
          </p>
          <div class="btn-row">{dl_btn}</div>
        </section>"""
        return page_wrap('ASX 200', 'asx', content, auto_refresh=(running and jname == 'ASX Download'))

    sparklines  = get_asx_sparklines_batch()
    latest      = get_asx_latest_prices()
    with_data   = get_tickers_with_data()

    rows_html = ''
    for ticker in sorted(ASX_200):
        closes  = sparklines.get(ticker, [])
        price   = latest.get(ticker)
        svg     = sparkline_svg(closes)
        price_s = f'A${price:.3f}' if price else '—'
        has_row = ticker in with_data
        rows_html += f"""
        <tr class="asx-row" data-ticker="{ticker}" style="cursor:{'pointer' if has_row else 'default'}">
          <td>
            <div style="display:flex;align-items:center;gap:10px">
              <strong style="color:#60a5fa;min-width:52px">{ticker}</strong>
              {svg if has_row else ''}
            </div>
          </td>
          <td style="font-weight:600">{price_s}</td>
          <td style="color:#555;font-size:.78rem">ASX</td>
        </tr>"""

    last_log = get_log()
    log_section = ''
    if running and jname == 'ASX Download':
        log_section = f'<section><h2>Download Log (live)</h2><pre>{last_log.replace("<","&lt;")}</pre></section>'
    elif 'ASX Data Download' in last_log:
        log_section = f'<section><h2>Last Download Log</h2><pre>{last_log.replace("<","&lt;")}</pre></section>'

    chart_js = """
    <script src="https://unpkg.com/lightweight-charts@4.1.3/dist/lightweight-charts.standalone.production.js"></script>
    <script>
    document.querySelectorAll('.asx-row').forEach(row => {
      row.addEventListener('click', () => {
        const ticker = row.dataset.ticker;
        const existId = 'adrop-' + ticker;
        const exist = document.getElementById(existId);
        if (exist) { exist.remove(); row.classList.remove('active'); return; }
        document.querySelectorAll('.asx-drop').forEach(d => d.remove());
        document.querySelectorAll('.asx-row.active').forEach(r => r.classList.remove('active'));
        row.classList.add('active');
        const drop = document.createElement('tr');
        drop.id = existId; drop.className = 'asx-drop';
        drop.innerHTML = `<td colspan="3" style="background:#080a10;padding:16px 20px">
          <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:10px">
            <span style="color:#fff;font-weight:700;font-size:1rem">${ticker} <span style="color:#555;font-size:.78rem">ASX</span></span>
            <span style="color:#555;font-size:.75rem" id="as-${ticker}">Loading...</span>
          </div>
          <div id="am-${ticker}" style="height:340px;background:#0a0c14;border-radius:6px"></div>
          <div id="av-${ticker}" style="height:65px;background:#0a0c14;border-radius:6px;margin-top:3px"></div>
        </td>`;
        row.parentNode.insertBefore(drop, row.nextSibling);
        fetch('/api/asx-chart/' + ticker)
          .then(r => r.json())
          .then(data => {
            if (data.error) { document.getElementById('as-' + ticker).textContent = data.error; return; }
            document.getElementById('as-' + ticker).textContent = data.bars + ' bars · ' + data.date_range;
            const chart = LightweightCharts.createChart(document.getElementById('am-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: true },
              crosshair: { mode: LightweightCharts.CrosshairMode.Normal },
            });
            const candles = chart.addCandlestickSeries({
              upColor: '#22c55e', downColor: '#ef4444',
              borderUpColor: '#22c55e', borderDownColor: '#ef4444',
              wickUpColor: '#22c55e', wickDownColor: '#ef4444',
            });
            candles.setData(data.ohlcv);
            const ema5  = chart.addLineSeries({ color: '#60a5fa', lineWidth: 1, title: 'EMA5' });
            const ema26 = chart.addLineSeries({ color: '#f59e0b', lineWidth: 1, title: 'EMA26' });
            ema5.setData(data.ema5); ema26.setData(data.ema26);
            const barCount = data.ohlcv.length;
            chart.timeScale().setVisibleLogicalRange({ from: 0, to: barCount + Math.round(barCount * 0.9) });
            chart.priceScale('right').applyOptions({ scaleMargins: { top: 0.12, bottom: 0.18 } });
            const vc = LightweightCharts.createChart(document.getElementById('av-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: false },
            });
            const vs = vc.addHistogramSeries({ priceFormat: { type: 'volume' }, priceScaleId: '' });
            vs.priceScale().applyOptions({ scaleMargins: { top: 0.1, bottom: 0 } });
            vs.setData(data.volume); vc.timeScale().fitContent();
            chart.timeScale().subscribeVisibleLogicalRangeChange(r => vc.timeScale().setVisibleLogicalRange(r));
            vc.timeScale().subscribeVisibleLogicalRangeChange(r => chart.timeScale().setVisibleLogicalRange(r));
          })
          .catch(e => { document.getElementById('as-' + ticker).textContent = 'Failed: ' + e; });
      });
    });
    </script>"""

    # ── ASX breadth from sparklines ───────────────────────────────────────────
    def asx_breadth(n):
        up = down = flat = 0
        for t in sorted(ASX_200):
            c = sparklines.get(t, [])
            if len(c) > n:
                if   c[-1] > c[-1-n]: up   += 1
                elif c[-1] < c[-1-n]: down += 1
                else:                 flat += 1
        total = up + down + flat
        up_pct   = round(up   / total * 100, 1) if total else 0
        down_pct = round(down / total * 100, 1) if total else 0
        flat_pct = round(100 - up_pct - down_pct, 1)
        return up, down, flat, up_pct, down_pct, flat_pct

    ad_up, ad_dn, ad_fl, ad_up_pct, ad_dn_pct, ad_fl_pct = asx_breadth(1)
    aw_up, aw_dn, aw_fl, aw_up_pct, aw_dn_pct, aw_fl_pct = asx_breadth(5)
    am_up, am_dn, am_fl, am_up_pct, am_dn_pct, am_fl_pct = asx_breadth(21)

    asx_donut_html = ''
    for period, up_pct, dn_pct, fl_pct, up, dn in [
        ('Day',   ad_up_pct, ad_dn_pct, ad_fl_pct, ad_up, ad_dn),
        ('Week',  aw_up_pct, aw_dn_pct, aw_fl_pct, aw_up, aw_dn),
        ('Month', am_up_pct, am_dn_pct, am_fl_pct, am_up, am_dn),
    ]:
        pid = 'asx-' + period.lower()
        cs = 'position:absolute;top:50%;left:50%;transform:translate(-50%,-50%);font-size:1.6rem;font-weight:800;color:#fff;white-space:nowrap'
        asx_donut_html += (
            f'<div style="text-align:center">'
            f'<div style="font-size:.82rem;color:#aaa;font-weight:600;text-transform:uppercase;letter-spacing:.08em;margin-bottom:10px">{period}</div>'
            f'<div style="position:relative;width:150px;height:150px">'
            f'<canvas id="donut-{pid}" width="150" height="150"></canvas>'
            f'<div style="{cs}">{up_pct}%</div>'
            f'</div>'
            f'<div style="font-size:.88rem;margin-top:10px;font-weight:600">'
            f'<span style="color:#22c55e">&#9650; {up} up</span>'
            f'<span style="color:#555;margin:0 8px">/</span>'
            f'<span style="color:#ef4444">&#9660; {dn} down</span>'
            f'</div></div>'
        )

    # Updated rows with bigger fonts + day %
    rows_html2 = ''
    for ticker in sorted(ASX_200):
        closes  = sparklines.get(ticker, [])
        price   = latest.get(ticker)
        svg2    = sparkline_svg(closes)
        price_s = f'A${price:.3f}' if price else '—'
        has_row = ticker in with_data
        day_chg = ''
        if len(closes) >= 2:
            pct = (closes[-1] - closes[-2]) / closes[-2] * 100
            col = '#22c55e' if pct >= 0 else '#ef4444'
            day_chg = f'<span style="color:{col};font-size:.95rem;font-weight:600">{"+" if pct>=0 else ""}{pct:.2f}%</span>'
        rows_html2 += f"""
        <tr class="asx-row" data-ticker="{ticker}" style="cursor:{'pointer' if has_row else 'default'}">
          <td>
            <div style="display:flex;align-items:center;gap:12px">
              <strong style="color:#60a5fa;min-width:68px;font-size:1rem">{ticker}</strong>
              {svg2 if has_row else ''}
            </div>
          </td>
          <td style="font-weight:700;color:#fff;font-size:1rem">{price_s}</td>
          <td style="font-size:.95rem;font-weight:600">{day_chg}</td>
        </tr>"""

    content = f"""
    <script src="https://cdn.jsdelivr.net/npm/chart.js@4.4.0/dist/chart.umd.min.js"></script>
    <script src="https://unpkg.com/lightweight-charts@4.1.3/dist/lightweight-charts.standalone.production.js"></script>

    <!-- Dashboard header -->
    <section style="margin-bottom:20px">
      <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:14px">
        <span></span>
        <div class="btn-row">{dl_btn}</div>
      </div>

      <!-- STW area chart -->
      <div style="margin-bottom:18px">
        <div style="font-size:.78rem;color:#888;font-weight:600;margin-bottom:8px">
          STW &nbsp;<span style="color:#555;font-weight:400">— ASX 200 ETF · 60 Day</span>
        </div>
        <div id="asx-etf-area" style="height:220px;background:#0a0c14;border-radius:8px"></div>
      </div>

      <!-- Breadth donuts -->
      <div>
        <p style="font-size:.88rem;color:#888;margin-bottom:14px">
          Percentage of <strong style="color:#fff">ASX 200</strong> stocks moving up or down over each time period
        </p>
        <div style="display:flex;gap:28px;align-items:flex-start;flex-wrap:wrap">
          {asx_donut_html}
        </div>
      </div>

      <div style="margin-top:14px;font-size:.8rem;color:#444">
        {len(with_data)} tickers with data &nbsp;·&nbsp; click any row to expand chart
      </div>
    </section>

    <script>
    // ASX ETF chart
    (function(){{
      fetch('/api/asx-chart/STW')
        .then(r=>r.json())
        .then(data=>{{
          if(data.error||!data.ohlcv) return;
          const recent = data.ohlcv.slice(-60);
          const chart = LightweightCharts.createChart(document.getElementById('asx-etf-area'),{{
            layout:{{background:{{color:'#0a0c14'}},textColor:'#555'}},
            grid:{{vertLines:{{color:'#12141e'}},horzLines:{{color:'#12141e'}}}},
            rightPriceScale:{{borderColor:'#1a1d2e'}},
            timeScale:{{borderColor:'#1a1d2e',timeVisible:false}},
            crosshair:{{mode:LightweightCharts.CrosshairMode.Normal}},
            handleScroll:false, handleScale:false,
          }});
          const area = chart.addAreaSeries({{
            lineColor:'#22c55e', topColor:'#22c55e44',
            bottomColor:'#22c55e00', lineWidth:2,
          }});
          area.setData(recent.map(b=>({{time:b.time,value:b.close}})));
          chart.timeScale().fitContent();
        }}).catch(()=>{{}});
    }})();
    // Breadth donuts
    (function(){{
      const donuts = [
        {{ id:'donut-asx-day',   up:{ad_up_pct}, dn:{ad_dn_pct}, fl:{ad_fl_pct} }},
        {{ id:'donut-asx-week',  up:{aw_up_pct}, dn:{aw_dn_pct}, fl:{aw_fl_pct} }},
        {{ id:'donut-asx-month', up:{am_up_pct}, dn:{am_dn_pct}, fl:{am_fl_pct} }},
      ];
      donuts.forEach(d => {{
        const ctx = document.getElementById(d.id).getContext('2d');
        new Chart(ctx, {{
          type: 'doughnut',
          data: {{ datasets: [{{ data:[d.up,d.dn,d.fl],
            backgroundColor:['#22c55e','#ef4444','#1f2235'], borderWidth:0, hoverOffset:4 }}] }},
          options: {{
            cutout:'70%',
            animation:{{ animateRotate:true, duration:1200, easing:'easeInOutQuart' }},
            plugins:{{ legend:{{display:false}},
              tooltip:{{ callbacks:{{ label: ctx=>['Up','Down','Flat'][ctx.dataIndex]+': '+ctx.parsed+'%' }} }} }}
          }}
        }});
      }});
    }})();
    </script>

    {log_section}
    <section>
      <style>
        .asx-table {{ width:100%; border-collapse:collapse; font-size:.95rem; }}
        .asx-table th {{ text-align:left; padding:10px 14px; color:#777;
                        border-bottom:1px solid #2a2d3e; font-weight:500; cursor:pointer; user-select:none; font-size:.82rem; }}
        .asx-table th:hover {{ color:#aaa; }}
        .asx-table th.sort-asc::after  {{ content:' ▲'; font-size:.65rem; color:#60a5fa; }}
        .asx-table th.sort-desc::after {{ content:' ▼'; font-size:.65rem; color:#60a5fa; }}
        .asx-table td {{ padding:10px 14px; border-bottom:1px solid #151820; vertical-align:middle; }}
        .asx-table .asx-row:hover td {{ background:#1f2235; }}
        .asx-table .asx-row.active td {{ background:#1a2235; }}
        .asx-drop td {{ padding:0 !important; }}
      </style>
      <table class="asx-table">
        <thead><tr>
          <th onclick="sortAsx(this)">Ticker</th>
          <th onclick="sortAsx(this)">Price (AUD)</th>
          <th onclick="sortAsx(this)">Day %</th>
        </tr></thead>
        <tbody id="asx-tbody">{rows_html2}</tbody>
      </table>
    </section>
    <script>
    function sortAsx(th) {{
      const tbody = document.getElementById('asx-tbody');
      const idx = th.cellIndex;
      const asc = th.classList.contains('sort-desc');
      th.closest('thead').querySelectorAll('th').forEach(h => h.classList.remove('sort-asc','sort-desc'));
      th.classList.add(asc ? 'sort-asc' : 'sort-desc');
      const rows = Array.from(tbody.querySelectorAll('.asx-row'));
      rows.sort((a, b) => {{
        const av = a.cells[idx].textContent.trim();
        const bv = b.cells[idx].textContent.trim();
        const an = parseFloat(av.replace('A$','').replace('%','')), bn = parseFloat(bv.replace('A$','').replace('%',''));
        const cmp = isNaN(an) ? av.localeCompare(bv) : an - bn;
        return asc ? cmp : -cmp;
      }});
      rows.forEach(r => tbody.appendChild(r));
    }}
    </script>
    {chart_js}"""

    return page_wrap('ASX 200', 'asx', content, auto_refresh=(running and jname == 'ASX Download'))


@app.route('/asx/download')
def asx_download():
    if not is_admin():
        return redirect('/asx')
    start_asx_download_job()
    return redirect('/asx')


@app.route('/api/asx-chart/<ticker>')
def asx_chart_api(ticker):
    ticker = ticker.upper()
    rows = get_asx_chart_data(ticker)
    if not rows:
        return jsonify({'error': f'No data for {ticker}'})

    dates  = [str(r[0]) for r in rows]
    opens  = [float(r[1]) for r in rows]
    highs  = [float(r[2]) for r in rows]
    lows   = [float(r[3]) for r in rows]
    closes = [float(r[4]) for r in rows]
    vols   = [int(r[5]) if r[5] else 0 for r in rows]

    close_s = pd.Series(closes)
    ema5  = close_s.ewm(span=5,  adjust=False).mean().tolist()
    ema26 = close_s.ewm(span=26, adjust=False).mean().tolist()

    ohlcv  = [{'time': dates[i], 'open': opens[i], 'high': highs[i],
               'low': lows[i], 'close': closes[i]} for i in range(len(dates))]
    volume = [{'time': dates[i], 'value': vols[i],
               'color': '#22c55e44' if closes[i] >= opens[i] else '#ef444444'}
              for i in range(len(dates))]
    e5  = [{'time': dates[i], 'value': ema5[i]}  for i in range(len(dates))]
    e26 = [{'time': dates[i], 'value': ema26[i]} for i in range(len(dates))]

    return jsonify({
        'ohlcv': ohlcv, 'volume': volume, 'ema5': e5, 'ema26': e26,
        'bars': len(ohlcv),
        'date_range': f"{dates[0]} → {dates[-1]}" if dates else '',
    })


@app.route('/api/us-chart/<ticker>')
def us_chart_api(ticker):
    """
    JSON endpoint consumed by the inline LightweightCharts candlestick charts.

    Returns full OHLCV history from the prices table plus EMA5 and EMA26
    calculated in pandas (not stored in DB — computed fresh each request).
    Volume bars are coloured green/red based on whether that bar closed up or down.
    """
    ticker = ticker.upper()
    try:
        conn = get_connection()
        with conn.cursor() as cur:
            cur.execute("""
                SELECT date, open, high, low, close, volume
                FROM prices WHERE ticker = %s ORDER BY date ASC
            """, (ticker,))
            rows = cur.fetchall()
        conn.close()
    except Exception as e:
        return jsonify({'error': str(e)})

    if not rows:
        return jsonify({'error': f'No data for {ticker}'})

    dates  = [str(r[0]) for r in rows]
    opens  = [float(r[1]) for r in rows]
    highs  = [float(r[2]) for r in rows]
    lows   = [float(r[3]) for r in rows]
    closes = [float(r[4]) for r in rows]
    vols   = [int(r[5]) if r[5] else 0 for r in rows]

    close_s = pd.Series(closes)
    ema5  = close_s.ewm(span=5,  adjust=False).mean().tolist()
    ema26 = close_s.ewm(span=26, adjust=False).mean().tolist()

    ohlcv  = [{'time': dates[i], 'open': opens[i], 'high': highs[i],
               'low': lows[i], 'close': closes[i]} for i in range(len(dates))]
    volume = [{'time': dates[i], 'value': vols[i],
               'color': '#22c55e44' if closes[i] >= opens[i] else '#ef444444'}
              for i in range(len(dates))]
    e5  = [{'time': dates[i], 'value': ema5[i]}  for i in range(len(dates))]
    e26 = [{'time': dates[i], 'value': ema26[i]} for i in range(len(dates))]

    return jsonify({
        'ohlcv': ohlcv, 'volume': volume, 'ema5': e5, 'ema26': e26,
        'bars': len(ohlcv),
        'date_range': f"{dates[0]} → {dates[-1]}" if dates else '',
    })


@app.route('/api/channel-lines/<ticker>/<timeframe>')
def channel_lines_api(ticker, timeframe):
    """Return lower/upper channel line time-series for overlay on the chart."""
    import numpy as np
    ticker = ticker.upper()
    if timeframe not in PCHAN_CONFIGS:
        return jsonify({'error': 'invalid timeframe'})
    cfg = PCHAN_CONFIGS[timeframe]
    try:
        conn = get_connection()
        daily_df = get_ticker_daily(conn, ticker)
        conn.close()
    except Exception as e:
        return jsonify({'error': str(e)})

    if daily_df is None or len(daily_df) < 30:
        return jsonify({'error': 'not enough data'})

    if timeframe == 'weekly':
        df = resample_weekly(daily_df)
    elif timeframe == 'monthly':
        df = resample_monthly(daily_df)
    else:
        df = daily_df

    n_bars  = cfg['bars']
    lb      = cfg['pivot_lb']
    use_log = cfg['log_scale']
    max_w   = cfg['max_width']
    MIN_R2  = 0.65

    sub = df.tail(n_bars).reset_index()
    n   = len(sub)
    if n < max(20, n_bars // 4):
        return jsonify({'error': 'not enough bars'})

    # Weekly/monthly rows use period-start dates; daily uses actual date column
    dates = [str(sub.iloc[i]['date'])[:10] for i in range(n)]

    raw_h = sub['high'].values.astype(float)
    raw_l = sub['low'].values.astype(float)

    if use_log and (np.any(raw_l <= 0) or np.any(raw_h <= 0)):
        return jsonify({'error': 'non-positive prices'})

    wh = np.log(raw_h) if use_log else raw_h
    wl = np.log(raw_l) if use_log else raw_l
    x  = np.arange(n, dtype=float)

    ph = find_pivot_highs(wh.tolist(), lb)
    pl = find_pivot_lows(wl.tolist(), lb)
    if len(ph) < 2 or len(pl) < 2:
        return jsonify({'error': 'no channel'})

    low_slope, low_intercept, r2 = fit_line(
        [float(i) for i in pl], [float(wl[i]) for i in pl]
    )
    if low_slope is None or low_slope <= 0 or r2 < MIN_R2:
        return jsonify({'error': 'no channel'})

    lower_line = low_slope * x + low_intercept
    offsets    = [float(wh[i]) - float(lower_line[i]) for i in ph]
    if not offsets or max(offsets) <= 0:
        return jsonify({'error': 'no channel'})

    ch_offset  = float(max(offsets))
    upper_line = lower_line + ch_offset

    # Width filter — must match scanner
    c_low_now = float(lower_line[-1])
    if use_log:
        width_pct = float((np.exp(ch_offset) - 1) * 100)
    else:
        width_pct = float(ch_offset / abs(c_low_now) * 100) if c_low_now > 0 else 0.0
    if width_pct > max_w:
        return jsonify({'error': 'channel too wide'})

    # Convert to actual prices
    if use_log:
        lower_prices = [float(np.exp(v)) for v in lower_line]
        upper_prices = [float(np.exp(v)) for v in upper_line]
    else:
        lower_prices = [float(v) for v in lower_line]
        upper_prices = [float(v) for v in upper_line]

    lower_series = [{'time': dates[i], 'value': round(lower_prices[i], 4)} for i in range(n)]
    upper_series = [{'time': dates[i], 'value': round(upper_prices[i], 4)} for i in range(n)]

    return jsonify({'lower': lower_series, 'upper': upper_series, 'r2': round(r2, 3)})


# ─── ASX Picks ────────────────────────────────────────────────────────────────

@app.route('/asx/picks')
def asx_picks_page():
    positions = get_asx_picks()
    history   = get_asx_history()
    cash      = get_asx_account()
    port_val  = get_asx_portfolio_value(positions)
    total_val = cash + port_val
    total_pnl = total_val - 100_000.0

    # Daily P&L — compare today's close vs yesterday's close for each position
    daily_changes = get_asx_daily_changes([p['ticker'] for p in positions])
    daily_pnl_total = sum(
        p['shares'] * (daily_changes[p['ticker']][0] - daily_changes[p['ticker']][1])
        for p in positions if p['ticker'] in daily_changes
    )
    for p in positions:
        if p['ticker'] in daily_changes:
            today, prev = daily_changes[p['ticker']]
            p['daily_pnl'] = p['shares'] * (today - prev)
            p['daily_pct'] = ((today - prev) / prev * 100) if prev else 0
        else:
            p['daily_pnl'] = 0.0
            p['daily_pct'] = 0.0

    # Account summary bar
    pnl_color  = '#22c55e' if total_pnl >= 0 else '#ef4444'
    pnl_sign   = '+' if total_pnl >= 0 else ''
    dpnl_color = '#22c55e' if daily_pnl_total >= 0 else '#ef4444'
    dpnl_sign  = '+' if daily_pnl_total >= 0 else ''
    summary = f"""
    <div class="grid4" style="margin-bottom:24px">
      <div class="card">
        <div class="stat-label">Cash Available</div>
        <div class="stat-value" style="font-size:1.3rem">A${cash:,.2f}</div>
        <div class="stat-sub">of A$100,000 starting balance</div>
      </div>
      <div class="card">
        <div class="stat-label">Portfolio Value</div>
        <div class="stat-value" style="font-size:1.3rem">A${port_val:,.2f}</div>
        <div class="stat-sub">{len(positions)} open position{'s' if len(positions)!=1 else ''}</div>
      </div>
      <div class="card">
        <div class="stat-label">Total P&amp;L</div>
        <div class="stat-value" style="font-size:1.3rem;color:{pnl_color}">{pnl_sign}A${total_pnl:,.2f}</div>
        <div class="stat-sub" style="color:{pnl_color}">{pnl_sign}{total_pnl/1000:.1f}% on A$100k</div>
      </div>
      <div class="card">
        <div class="stat-label">Today's P&amp;L</div>
        <div class="stat-value" style="font-size:1.3rem;color:{dpnl_color}">{dpnl_sign}A${daily_pnl_total:,.2f}</div>
        <div class="stat-sub" style="color:{dpnl_color}">unrealised daily move</div>
      </div>
    </div>"""

    # Add new pick form (admin only)
    add_form = '' if not is_admin() else """
    <section>
      <h2>Add New ASX Pick</h2>
      <form method="POST" action="/asx/picks/buy" enctype="multipart/form-data">
        <div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(180px,1fr));gap:12px;margin-bottom:12px">
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Ticker *</label>
            <input name="ticker" placeholder="e.g. BHP" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Shares *</label>
            <input name="shares" type="number" step="0.0001" placeholder="e.g. 100" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Buy Price (AUD) *</label>
            <input name="buy_price" type="number" step="0.0001" placeholder="e.g. 45.00" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Target / Take Profit</label>
            <input name="target_price" type="number" step="0.0001" placeholder="e.g. 55.00" style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
        </div>
        <div style="margin-bottom:12px">
          <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Why I think it will go up</label>
          <textarea name="reason" rows="3" placeholder="Channel breakout forming, EMA squeeze on weekly..." style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.88rem;resize:vertical"></textarea>
        </div>
        <div style="margin-bottom:16px">
          <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">TradingView Chart Screenshot</label>
          <input name="chart_image" type="file" accept="image/*" style="color:#aaa;font-size:.85rem">
        </div>
        <button type="submit" class="btn btn-green">+ Add to ASX Portfolio</button>
      </form>
    </section>"""

    # Open positions
    pos_html = ''
    if positions:
        cards = ''
        for p in positions:
            pnl_c  = '#22c55e' if p['pnl'] >= 0 else '#ef4444'
            sign   = '+' if p['pnl'] >= 0 else ''
            tgt    = f"A${fmt_num(p['target_price'])}" if p['target_price'] else '—'
            upside = ''
            if p['target_price']:
                up = (p['target_price'] - p['current_price']) / p['current_price'] * 100
                upside = f"<span style='color:#60a5fa;font-size:.78rem'>({up:+.1f}% to target)</span>"

            img_html = ''
            if p['image_path']:
                img_html = f'<img src="/asx/picks/image/{p["image_path"]}" style="width:100%;border-radius:6px;margin-bottom:12px;border:1px solid #2a2d3e">'

            reason_html = f'<p style="color:#aaa;font-size:.83rem;margin-bottom:12px;line-height:1.5">{p["reason"]}</p>' if p['reason'] else ''

            if is_admin():
                pticker = p['ticker']
                action_html = f"""
                <div style="display:flex;gap:8px;align-items:center">
                  <button class="btn btn-amber" style="padding:7px 16px"
                    onclick="openSellModal({p['id']},'{pticker}',{p['shares']},{p['current_price']:.4f},'/asx/picks/sell/{p['id']}')">Sell</button>
                </div>"""
            else:
                action_html = ''

            dc     = p['daily_pnl']
            dc_c   = '#22c55e' if dc >= 0 else '#ef4444'
            dc_s   = '+' if dc >= 0 else ''
            daily_badge = f'<span style="font-size:.78rem;font-weight:600;color:{dc_c};background:{dc_c}18;padding:2px 8px;border-radius:4px">{dc_s}A${dc:,.2f} today ({dc_s}{p["daily_pct"]:.2f}%)</span>'

            cards += f"""
            <div class="card" style="margin-bottom:16px">
              <div style="display:flex;justify-content:space-between;align-items:flex-start;flex-wrap:wrap;gap:8px;margin-bottom:8px">
                <div>
                  <span style="font-size:1.3rem;font-weight:700;color:#60a5fa">{p['ticker']}</span>
                  <span style="color:#555;font-size:.78rem;margin-left:10px">ASX · bought {p['bought_date']}</span>
                </div>
                <span style="font-size:1.1rem;font-weight:700;color:{pnl_c}">{sign}A${p['pnl']:,.2f} ({sign}{p['pnl_pct']:.1f}%)</span>
              </div>
              <div style="margin-bottom:12px">{daily_badge}</div>
              {img_html}
              {reason_html}
              <div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(130px,1fr));gap:8px;margin-bottom:14px;font-size:.83rem">
                <div><span style="color:#555">Shares</span><br><strong>{fmt_num(p['shares'])}</strong></div>
                <div><span style="color:#555">Buy Price</span><br><strong>A${fmt_num(p['buy_price'])}</strong></div>
                <div><span style="color:#555">Current</span><br><strong>A${fmt_num(p['current_price'])}</strong></div>
                <div><span style="color:#555">Cost Basis</span><br><strong>A${p['cost']:,.2f}</strong></div>
                <div><span style="color:#555">Market Value</span><br><strong>A${p['value']:,.2f}</strong></div>
                <div><span style="color:#555">Target</span><br><strong>{tgt}</strong> {upside}</div>
              </div>
              {action_html}
            </div>"""
        pos_html = f'<section><h2>Open Positions ({len(positions)})</h2>{cards}</section>'
    else:
        pos_html = '<section><h2>Open Positions</h2><p class="note">No open positions yet. Add your first ASX pick above!</p></section>'

    # Trade history
    hist_html = ''
    if history:
        rows = ''
        for t in history:
            action_color = '#22c55e' if t['action'] == 'BUY' else '#ef4444'
            pnl_str = ''
            if t['pnl'] is not None:
                pnl_color = '#22c55e' if t['pnl'] >= 0 else '#ef4444'
                pnl_str = f'<span style="color:{pnl_color}">{("+" if t["pnl"]>=0 else "")}A${t["pnl"]:,.2f}</span>'
            rows += f"""<tr>
              <td>{t['trade_date']}</td>
              <td><strong style="color:#60a5fa">{t['ticker']}</strong></td>
              <td><span style="color:{action_color};font-weight:700">{t['action']}</span></td>
              <td>{fmt_num(t['shares'])}</td>
              <td>A${fmt_num(t['price'])}</td>
              <td>A${t['total']:,.2f}</td>
              <td>{pnl_str}</td>
            </tr>"""
        hist_html = f"""
        <section>
          <h2>Trade History</h2>
          <style>
            table{{width:100%;border-collapse:collapse;font-size:.83rem}}
            th{{text-align:left;padding:8px 10px;color:#555;border-bottom:1px solid #2a2d3e;font-weight:500}}
            td{{padding:8px 10px;border-bottom:1px solid #151820}}
            tr:hover td{{background:#1f2235}}
          </style>
          <table>
            <tr><th>Date</th><th>Ticker</th><th>Action</th><th>Shares</th><th>Price</th><th>Total</th><th>P&L</th></tr>
            {rows}
          </table>
        </section>"""

    sell_modal = """
    <div id="sell-modal" style="display:none;position:fixed;inset:0;background:rgba(0,0,0,.75);z-index:9000;align-items:center;justify-content:center">
      <div style="background:#13151f;border:1px solid #2a2d3e;border-radius:12px;padding:28px;width:100%;max-width:500px;margin:20px">
        <h3 id="sell-modal-title" style="margin:0 0 20px">Sell Position</h3>
        <form id="sell-form" method="POST" enctype="multipart/form-data">
          <div style="margin-bottom:14px">
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Sell Price *</label>
            <input id="sell-price-input" name="sell_price" type="number" step="0.0001" required
              style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div style="margin-bottom:14px">
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Why I sold</label>
            <textarea name="sell_reason" rows="4" placeholder="Stop loss hit, thesis broke, took profit at target..."
              style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.88rem;resize:vertical"></textarea>
          </div>
          <div style="margin-bottom:20px">
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Chart Screenshot (sell setup)</label>
            <input name="sell_chart" type="file" accept="image/*" style="color:#aaa;font-size:.85rem">
          </div>
          <div style="display:flex;gap:10px">
            <button type="submit" class="btn btn-amber" style="flex:1">Confirm Sell</button>
            <button type="button" class="btn" style="flex:1;background:#252839" onclick="closeSellModal()">Cancel</button>
          </div>
        </form>
      </div>
    </div>
    <script>
    function openSellModal(pickId, ticker, shares, currentPrice, action) {
      document.getElementById('sell-modal-title').textContent = 'Sell ' + shares + ' shares of ' + ticker;
      document.getElementById('sell-price-input').value = currentPrice;
      document.getElementById('sell-form').action = action;
      document.getElementById('sell-modal').style.display = 'flex';
    }
    function closeSellModal() {
      document.getElementById('sell-modal').style.display = 'none';
    }
    document.addEventListener('keydown', function(e) {
      if (e.key === 'Escape') closeSellModal();
    });
    </script>"""

    msg = request.args.get('msg', '')
    msg_html = f'<div style="background:#1a2e1a;border:1px solid #22c55e;border-radius:8px;padding:12px 16px;margin-bottom:20px;color:#86efac">{msg}</div>' if msg else ''
    err = request.args.get('err', '')
    err_html = f'<div class="err-box">{err}</div>' if err else ''

    content = err_html + msg_html + summary + add_form + pos_html + hist_html + sell_modal
    return page_wrap("Jimmy's ASX Picks", 'asxpicks', content)


@app.route('/asx/picks/buy', methods=['POST'])
def asx_picks_buy():
    if not is_admin():
        return redirect('/asx/picks')
    ticker     = request.form.get('ticker', '').strip().upper()
    shares     = float(request.form.get('shares', 0))
    buy_price  = float(request.form.get('buy_price', 0))
    target     = request.form.get('target_price', '').strip()
    reason     = request.form.get('reason', '').strip()
    target_val = float(target) if target else None

    image_filename = ''
    file = request.files.get('chart_image')
    if file and file.filename:
        ext = os.path.splitext(file.filename)[1].lower()
        image_filename = f"asx_{ticker}_{uuid.uuid4().hex[:8]}{ext}"
        os.makedirs(UPLOADS_DIR, exist_ok=True)
        file.save(os.path.join(UPLOADS_DIR, image_filename))

    ok, result = buy_asx_stock(ticker, shares, buy_price, target_val, reason, image_filename)
    if ok:
        return redirect(f'/asx/picks?msg=Bought+{shares}+shares+of+{ticker}+at+A${buy_price:.4f}')
    return redirect(f'/asx/picks?err={result}')


@app.route('/asx/picks/image/<filename>')
def asx_picks_image(filename):
    return send_from_directory(UPLOADS_DIR, filename)


@app.route('/asx/picks/sell/<int:pick_id>', methods=['POST'])
def asx_picks_sell(pick_id):
    if not is_admin():
        return redirect('/asx/picks')
    sell_price  = float(request.form.get('sell_price', 0))
    sell_reason = request.form.get('sell_reason', '').strip()

    sell_image = ''
    file = request.files.get('sell_chart')
    if file and file.filename:
        ext = os.path.splitext(file.filename)[1].lower()
        sell_image = f"sell_{pick_id}_{uuid.uuid4().hex[:8]}{ext}"
        os.makedirs(UPLOADS_DIR, exist_ok=True)
        file.save(os.path.join(UPLOADS_DIR, sell_image))

    ok, result = sell_asx_stock(pick_id, sell_price, sell_reason, sell_image)
    if ok:
        sign = '+' if result >= 0 else ''
        return redirect(f'/asx/picks?msg=Sold+position+P%26L+{sign}A${result:.2f}')
    return redirect(f'/asx/picks?err={result}')


# ─── Trade Journal ────────────────────────────────────────────────────────────

@app.route('/journal')
def journal_page():
    msg = request.args.get('msg', '')
    err = request.args.get('err', '')
    msg_html = f'<div style="background:#1a2e1a;border:1px solid #22c55e;border-radius:8px;padding:12px 16px;margin-bottom:20px;color:#86efac">{msg}</div>' if msg else ''
    err_html = f'<div class="err-box">{err}</div>' if err else ''

    us_trades  = get_closed_trades()
    asx_trades = get_closed_asx_trades()
    all_trades = us_trades + asx_trades
    all_trades.sort(key=lambda t: t['sell_date'], reverse=True)

    total   = len(all_trades)
    wins    = sum(1 for t in all_trades if t['pnl'] >= 0)
    losses  = total - wins
    total_pnl = sum(t['pnl'] for t in all_trades)
    win_rate  = (wins / total * 100) if total else 0
    pnl_color = '#22c55e' if total_pnl >= 0 else '#ef4444'
    pnl_sign  = '+' if total_pnl >= 0 else ''

    stats = f"""
    <div class="grid4" style="margin-bottom:28px">
      <div class="card">
        <div class="stat-label">Closed Trades</div>
        <div class="stat-value">{total}</div>
      </div>
      <div class="card">
        <div class="stat-label">Win Rate</div>
        <div class="stat-value" style="color:{'#22c55e' if win_rate>=50 else '#ef4444'}">{win_rate:.0f}%</div>
        <div class="stat-sub">{wins}W / {losses}L</div>
      </div>
      <div class="card">
        <div class="stat-label">Total Realised P&amp;L</div>
        <div class="stat-value" style="color:{pnl_color}">{pnl_sign}${total_pnl:,.2f}</div>
      </div>
      <div class="card">
        <div class="stat-label">Avg P&amp;L per Trade</div>
        <div class="stat-value" style="color:{pnl_color}">{pnl_sign}${(total_pnl/total):,.2f}</div>
      </div>
    </div>""" if total else ''

    cards = ''
    for t in all_trades:
        pnl_c = '#22c55e' if t['pnl'] >= 0 else '#ef4444'
        sign  = '+' if t['pnl'] >= 0 else ''
        market_badge = f'<span style="font-size:.72rem;padding:2px 8px;border-radius:4px;background:#1e3a5f;color:#60a5fa;font-weight:600">{t["market"]}</span>'

        buy_img_html = ''
        if t['buy_image']:
            buy_img_html = f'<img src="/picks/image/{t["buy_image"]}" onclick="openLightbox(this.src)" style="width:100%;border-radius:6px;margin-bottom:8px;border:1px solid #2a2d3e;cursor:pointer">'

        sell_img_html = ''
        if t['sell_image']:
            sell_img_html = f'<img src="/picks/image/{t["sell_image"]}" onclick="openLightbox(this.src)" style="width:100%;border-radius:6px;margin-bottom:8px;border:1px solid #2a2d3e;cursor:pointer">'

        buy_reason_html  = f'<p style="color:#aaa;font-size:.83rem;line-height:1.5;margin:0">{t["buy_reason"]}</p>'  if t['buy_reason']  else ''
        sell_reason_html = f'<p style="color:#aaa;font-size:.83rem;line-height:1.5;margin:0">{t["sell_reason"]}</p>' if t['sell_reason'] else ''
        tid = t['id']
        tmkt = t['market']
        delete_btn = f'<form method="POST" action="/journal/delete/{tid}/{tmkt}" onsubmit="return confirm(\'Delete this trade?\')"><button type="submit" style="font-size:.75rem;padding:4px 12px;background:transparent;border:1px solid #3a2020;border-radius:5px;color:#666;cursor:pointer">Delete</button></form>' if is_admin() else ''

        cards += f"""
        <div class="card" style="margin-bottom:20px">
          <div style="display:flex;justify-content:space-between;align-items:flex-start;flex-wrap:wrap;gap:8px;margin-bottom:12px">
            <div style="display:flex;align-items:center;gap:10px">
              <span style="font-size:1.3rem;font-weight:700;color:#60a5fa">{t['ticker']}</span>
              {market_badge}
            </div>
            <span style="font-size:1.1rem;font-weight:700;color:{pnl_c}">{sign}${t['pnl']:,.2f} ({sign}{t['pnl_pct']:.1f}%)</span>
          </div>

          <div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(120px,1fr));gap:8px;margin-bottom:16px;font-size:.83rem">
            <div><span style="color:#555">Bought</span><br><strong>{t['bought_date']}</strong></div>
            <div><span style="color:#555">Sold</span><br><strong>{t['sell_date']}</strong></div>
            <div><span style="color:#555">Buy Price</span><br><strong>${t['buy_price']:.4f}</strong></div>
            <div><span style="color:#555">Sell Price</span><br><strong>${t['sell_price']:.4f}</strong></div>
            <div><span style="color:#555">Shares</span><br><strong>{t['shares']:,.2f}</strong></div>
          </div>

          <div style="display:grid;grid-template-columns:1fr 1fr;gap:16px;margin-bottom:14px">
            <div>
              <div style="font-size:.72rem;color:#555;text-transform:uppercase;letter-spacing:.05em;margin-bottom:6px">Buy Setup</div>
              {buy_img_html}
              {buy_reason_html}
            </div>
            <div>
              <div style="font-size:.72rem;color:#555;text-transform:uppercase;letter-spacing:.05em;margin-bottom:6px">Sell Setup</div>
              {sell_img_html}
              {sell_reason_html}
            </div>
          </div>
          {delete_btn}
        </div>"""

    if not all_trades:
        cards = '<p class="note">No closed trades yet. Sell a position from Jimmy\'s Picks or ASX Picks to start your journal.</p>'

    lightbox = """
    <div id="lightbox" onclick="closeLightbox()" style="display:none;position:fixed;inset:0;background:rgba(0,0,0,.9);z-index:9999;align-items:center;justify-content:center;cursor:zoom-out">
      <img id="lightbox-img" style="max-width:92vw;max-height:92vh;border-radius:8px;box-shadow:0 0 60px rgba(0,0,0,.8)">
    </div>
    <script>
    function openLightbox(src){document.getElementById('lightbox-img').src=src;document.getElementById('lightbox').style.display='flex';}
    function closeLightbox(){document.getElementById('lightbox').style.display='none';}
    document.addEventListener('keydown',function(e){if(e.key==='Escape')closeLightbox();});
    </script>"""

    add_form = '' if not is_admin() else """
    <section>
      <h2>Add Closed Trade</h2>
      <form method="POST" action="/journal/add" enctype="multipart/form-data">
        <div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(160px,1fr));gap:12px;margin-bottom:14px">
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Market *</label>
            <select name="market" style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
              <option value="US">US</option>
              <option value="ASX">ASX</option>
            </select>
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Ticker *</label>
            <input name="ticker" placeholder="e.g. AAPL" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Shares *</label>
            <input name="shares" type="number" step="0.0001" placeholder="e.g. 100" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Buy Price *</label>
            <input name="buy_price" type="number" step="0.0001" placeholder="e.g. 150.00" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Buy Date *</label>
            <input name="buy_date" type="date" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Sell Price *</label>
            <input name="sell_price" type="number" step="0.0001" placeholder="e.g. 180.00" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Sell Date *</label>
            <input name="sell_date" type="date" required style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.9rem">
          </div>
        </div>
        <div style="display:grid;grid-template-columns:1fr 1fr;gap:16px;margin-bottom:14px">
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Why I bought</label>
            <textarea name="buy_reason" rows="3" placeholder="Channel forming, EMA squeeze..."
              style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.88rem;resize:vertical"></textarea>
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Why I sold</label>
            <textarea name="sell_reason" rows="3" placeholder="Stop loss hit, took profit..."
              style="width:100%;padding:8px 10px;background:#0a0c14;border:1px solid #2a2d3e;border-radius:6px;color:#fff;font-size:.88rem;resize:vertical"></textarea>
          </div>
        </div>
        <div style="display:grid;grid-template-columns:1fr 1fr;gap:16px;margin-bottom:18px">
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Buy Chart</label>
            <input name="buy_chart" type="file" accept="image/*" style="color:#aaa;font-size:.85rem">
          </div>
          <div>
            <label style="font-size:.78rem;color:#666;display:block;margin-bottom:4px">Sell Chart</label>
            <input name="sell_chart" type="file" accept="image/*" style="color:#aaa;font-size:.85rem">
          </div>
        </div>
        <button type="submit" class="btn btn-green">+ Add to Journal</button>
      </form>
    </section>"""

    content = f"""
    {err_html}{msg_html}
    {add_form}
    <section>
      <h2>Closed Trades</h2>
      <p style="color:#555;font-size:.88rem;margin-bottom:24px">Every closed trade — the good and the bad. Honesty builds trust.</p>
      {stats}
      {cards}
    </section>
    {lightbox}"""

    return page_wrap('Trade Journal', 'journal', content)


@app.route('/journal/add', methods=['POST'])
def journal_add():
    if not is_admin():
        return redirect('/journal')

    market     = request.form.get('market', 'US')
    ticker     = request.form.get('ticker', '').strip().upper()
    shares     = request.form.get('shares', '0')
    buy_price  = request.form.get('buy_price', '0')
    buy_date   = request.form.get('buy_date', '')
    buy_reason = request.form.get('buy_reason', '').strip()
    sell_price = request.form.get('sell_price', '0')
    sell_date  = request.form.get('sell_date', '')
    sell_reason = request.form.get('sell_reason', '').strip()

    buy_image = ''
    file = request.files.get('buy_chart')
    if file and file.filename:
        ext = os.path.splitext(file.filename)[1].lower()
        buy_image = f"buy_{ticker}_{uuid.uuid4().hex[:8]}{ext}"
        os.makedirs(UPLOADS_DIR, exist_ok=True)
        file.save(os.path.join(UPLOADS_DIR, buy_image))

    sell_image = ''
    file = request.files.get('sell_chart')
    if file and file.filename:
        ext = os.path.splitext(file.filename)[1].lower()
        sell_image = f"sell_{ticker}_{uuid.uuid4().hex[:8]}{ext}"
        os.makedirs(UPLOADS_DIR, exist_ok=True)
        file.save(os.path.join(UPLOADS_DIR, sell_image))

    if market == 'ASX':
        ok, result = add_manual_closed_asx_trade(
            ticker, shares, buy_price, buy_date, buy_reason, buy_image,
            sell_price, sell_date, sell_reason, sell_image)
    else:
        ok, result = add_manual_closed_trade(
            ticker, shares, buy_price, buy_date, buy_reason, buy_image,
            sell_price, sell_date, sell_reason, sell_image)

    if ok:
        sign = '+' if result >= 0 else ''
        return redirect(f'/journal?msg={ticker}+added+to+journal.+P%26L:+{sign}${result:.2f}')
    return redirect(f'/journal?err={result}')


@app.route('/journal/delete/<int:pick_id>/<market>', methods=['POST'])
def journal_delete(pick_id, market):
    if not is_admin():
        return redirect('/journal')
    if market == 'ASX':
        delete_closed_asx_trade(pick_id)
    else:
        delete_closed_trade(pick_id)
    return redirect('/journal?msg=Trade+deleted')


# ─── Fader Scanner ────────────────────────────────────────────────────────────

def _run_fader_scan_job():
    global _job_running, _job_name
    with open(LOG_FILE, 'w') as f:
        f.write(f"=== Fader Scan ===\nStarted: {datetime.now()}\n\n")
    try:
        run_fader_scan(log_callback=lambda m: open(LOG_FILE, 'a').write(m))
    except Exception as e:
        with open(LOG_FILE, 'a') as f:
            f.write(f"\nERROR: {e}\n")
    finally:
        with _job_lock:
            _job_running = False
            _job_name    = ''


def start_fader_scan():
    global _job_running, _job_name
    with _job_lock:
        if _job_running:
            return False
        _job_running = True
        _job_name    = 'Fader Scan'
    threading.Thread(target=_run_fader_scan_job, daemon=True).start()
    return True


@app.route('/fader')
def fader_page():
    with _job_lock:
        running = _job_running

    last = load_last_fader_results()

    run_btn = ''
    spinner = ''
    if is_admin():
        if running:
            run_btn = '<span class="btn btn-off">⏳ Scan Running…</span>'
            spinner = """
            <div id="scanner-spinner" style="text-align:center;padding:48px 20px">
              <style>
                @keyframes spin  { to { transform: rotate(360deg); } }
                @keyframes pulse { 0%,100%{opacity:.3} 50%{opacity:1} }
                @keyframes ticker-scroll {
                  0%   { content: "Scanning tickers…"; }
                  33%  { content: "Crunching channels…"; }
                  66%  { content: "Checking fader signals…"; }
                  100% { content: "Almost there…"; }
                }
                .spin-ring {
                  width: 72px; height: 72px; margin: 0 auto 24px;
                  border: 5px solid #2a2d3e;
                  border-top-color: #3b82f6;
                  border-right-color: #22c55e;
                  border-radius: 50%;
                  animation: spin 1s linear infinite;
                }
                .spin-dot {
                  display: inline-block; width: 8px; height: 8px;
                  border-radius: 50%; background: #3b82f6; margin: 0 3px;
                  animation: pulse 1.2s ease-in-out infinite;
                }
                .spin-dot:nth-child(2) { animation-delay: .2s; background:#22c55e; }
                .spin-dot:nth-child(3) { animation-delay: .4s; background:#f59e0b; }
              </style>
              <div class="spin-ring"></div>
              <div style="font-size:1rem;font-weight:600;color:#fff;margin-bottom:8px">
                Running Fader Scan
              </div>
              <div style="font-size:.83rem;color:#555;margin-bottom:16px" id="scan-msg">
                Scanning up to 3000+ tickers through 3 filters…
              </div>
              <div>
                <span class="spin-dot"></span>
                <span class="spin-dot"></span>
                <span class="spin-dot"></span>
              </div>
              <div style="margin-top:20px;font-size:.75rem;color:#444">
                Page auto-refreshes every 5s · results appear when done
              </div>
            </div>
            <script>
              const messages = [
                "Scanning up to 3000+ tickers through 3 filters…",
                "① Checking channel squeeze (EMA5/EMA26/ATR)…",
                "② Calculating fader signal (JMA + WMA chain)…",
                "③ Finding stocks at 25% of their dollar range…",
                "Sorting by closest to the 25% level…",
                "Almost done, hang tight…"
              ];
              let idx = 0;
              const el = document.getElementById('scan-msg');
              setInterval(() => {
                idx = (idx + 1) % messages.length;
                el.style.opacity = 0;
                setTimeout(() => { el.textContent = messages[idx]; el.style.opacity = 1; }, 300);
              }, 3000);
              el.style.transition = 'opacity 0.3s';
            </script>"""
        else:
            run_btn = '<a href="/run-fader" class="btn btn-blue">▶ Run Fader Scan</a>'

    # Build results table
    table = ''
    scan_info = ''
    if last:
        scan_info = (f'<p class="note" style="margin-bottom:16px">'
                     f'Last scan: {last["scan_date"]} — '
                     f'<strong style="color:#fff">{last["total"]}</strong> setups found</p>')
        if last['results']:
            rows = ''
            for r in last['results']:
                rows += f"""<tr>
                  <td><a href="/chart/{r['ticker']}" style="color:#60a5fa;font-weight:700">{r['ticker']}</a></td>
                  <td style="color:#fff">${r['price']:.2f}</td>
                  <td style="color:#aaa">{r['range']}</td>
                  <td style="color:#f59e0b">{r['position_pct']:.1f}%</td>
                  <td style="color:#86efac">${r['L25']:.2f}</td>
                  <td style="color:#22c55e">${r['L75']:.2f}</td>
                  <td style="color:#ef4444">${r['L0']:.2f}</td>
                  <td style="color:#22c55e;font-weight:600">{r['rr']:.1f}x</td>
                </tr>"""
            table = f"""
            <style>
              .fader-table {{ width:100%; border-collapse:collapse; font-size:.83rem }}
              .fader-table th {{ text-align:left; padding:8px 12px; color:#555;
                                 border-bottom:1px solid #2a2d3e; font-weight:500 }}
              .fader-table td {{ padding:8px 12px; border-bottom:1px solid #151820 }}
              .fader-table tr:hover td {{ background:#1f2235 }}
            </style>
            <table class="fader-table">
              <tr>
                <th>Ticker</th><th>Price</th><th>Range</th><th>Pos%</th>
                <th>25% Level</th><th>Target 75%</th><th>Stop 0%</th><th>R:R</th>
              </tr>
              {rows}
            </table>"""
        else:
            table = '<p class="note">No setups found in last scan.</p>'

    content = f"""
    <div style="margin-bottom:20px;display:flex;align-items:center;gap:12px;flex-wrap:wrap">
      {run_btn}
      <span style="font-size:.78rem;color:#555">
        Conditions: channel printing (daily) · fader green · price at 25% of dollar range
      </span>
    </div>
    {spinner}

    <section style="margin-bottom:20px">
      <h2>How it works</h2>
      <div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(200px,1fr));gap:12px;font-size:.83rem">
        <div class="card" style="padding:14px">
          <div style="color:#3b82f6;font-weight:700;margin-bottom:6px">① Channel</div>
          <div style="color:#aaa">EMA(5)/EMA(26) compressed within ATR — stock is coiling, low volatility squeeze</div>
        </div>
        <div class="card" style="padding:14px">
          <div style="color:#22c55e;font-weight:700;margin-bottom:6px">② Fader Green</div>
          <div style="color:#aaa">Fader line rising — JMA + WMA-chain signal turning bullish inside the squeeze</div>
        </div>
        <div class="card" style="padding:14px">
          <div style="color:#f59e0b;font-weight:700;margin-bottom:6px">③ 25% of Range</div>
          <div style="color:#aaa">Price sitting at the natural settling level — e.g. $1.25 in the $1–$2 range. Target: 75% level</div>
        </div>
      </div>
    </section>

    <section>
      <h2>Fader Scan Results</h2>
      {scan_info}
      {table if table else '<p class="note">No scan run yet. Click Run Fader Scan above.</p>'}
    </section>
    """
    return page_wrap('Fader Scan', 'fader', content, auto_refresh=running)


@app.route('/run-fader')
def run_fader_route():
    if not is_admin():
        return redirect('/fader')
    start_fader_scan()
    return redirect('/fader')


# ─── Wick Scanner ─────────────────────────────────────────────────────────────

def _run_wick_scan_job():
    global _job_running, _job_name
    with open(LOG_FILE, 'w') as f:
        f.write(f"=== Wick Scan ===\nStarted: {datetime.now()}\n\n")
    try:
        run_wick_scan(log_callback=lambda m: open(LOG_FILE, 'a').write(m))
    except Exception as e:
        with open(LOG_FILE, 'a') as f:
            f.write(f"\nERROR: {e}\n")
    finally:
        with _job_lock:
            _job_running = False
            _job_name    = ''


def start_wick_scan():
    global _job_running, _job_name
    with _job_lock:
        if _job_running:
            return False
        _job_running = True
        _job_name    = 'Wick Scan'
    threading.Thread(target=_run_wick_scan_job, daemon=True).start()
    return True


@app.route('/run-wick')
def run_wick():
    if not is_admin():
        return redirect('/admin')
    start_wick_scan()
    return redirect('/wick')


@app.route('/wick')
def wick_page():
    if not is_admin():
        return redirect('/')

    with _job_lock:
        running = _job_running
        jname   = _job_name

    last = load_last_wick_results()

    if running and jname == 'Wick Scan':
        run_btn = '<span class="btn btn-off">⏳ Scanning…</span>'
    elif running:
        run_btn = '<span class="btn btn-off">Another job running</span>'
    else:
        run_btn = '<a href="/run-wick" class="btn btn-blue">▶ Run Wick Scan</a>'

    def score_color(s):
        if s >= 8:  return '#22c55e'
        if s >= 5:  return '#f59e0b'
        return '#555'

    rows_html = ''
    if last and last.get('results'):
        for r in last['results']:
            sc   = r['score']
            gc   = '#22c55e' if r['gain_pct'] >= 0 else '#ef4444'
            gs   = '+' if r['gain_pct'] >= 0 else ''
            held = r['weeks_held']
            rows_html += f"""
            <tr class="wick-row" data-ticker="{r['ticker']}" data-wick-date="{r['wick_date']}">
              <td><strong style="color:#60a5fa;font-size:1rem">{r['ticker']}</strong></td>
              <td style="color:#aaa">{r['wick_date']}</td>
              <td style="text-align:center">
                <span style="background:{score_color(sc)};color:#fff;padding:3px 10px;
                             border-radius:12px;font-weight:700;font-size:.85rem">{sc}</span>
              </td>
              <td style="color:#fff;font-weight:600">{r['wick_ratio']}×</td>
              <td style="color:#aaa">{held}w</td>
              <td style="color:#888">{r['close_pct']}%</td>
              <td style="color:#fff;font-weight:600">${r['current_price']:,.4f}</td>
              <td style="color:{gc};font-weight:700">{gs}{r['gain_pct']:.2f}%</td>
            </tr>"""

    scan_info = ''
    if last:
        scan_info = (f"Last scan: {last['scan_date']} &nbsp;·&nbsp; "
                     f"{last['total']} signals from {last['tickers_scanned']} tickers")

    chart_js = """
    <script src="https://unpkg.com/lightweight-charts@4.1.3/dist/lightweight-charts.standalone.production.js"></script>
    <script>
    // LightweightCharts v4 series primitive — paneViews() → renderer() → draw()
    class VerticalLineRenderer {
      constructor(time, color, chart) {
        this._time = time; this._color = color; this._chart = chart;
      }
      draw(target) {
        const x = this._chart.timeScale().timeToCoordinate(this._time);
        if (x === null) return;
        target.useBitmapCoordinateSpace(scope => {
          const ctx = scope.context;
          const xb = Math.round(x * scope.horizontalPixelRatio);
          ctx.save();
          ctx.beginPath();
          ctx.moveTo(xb, 0);
          ctx.lineTo(xb, scope.bitmapSize.height);
          ctx.strokeStyle = this._color;
          ctx.lineWidth = Math.round(2 * scope.horizontalPixelRatio);
          ctx.setLineDash([6, 4]);
          ctx.stroke();
          ctx.restore();
        });
      }
    }
    class VerticalLinePaneView {
      constructor(time, color, chart) {
        this._renderer = new VerticalLineRenderer(time, color, chart);
      }
      renderer() { return this._renderer; }
      zOrder()   { return 'normal'; }
    }
    class VerticalLine {
      constructor(time, color = '#ef4444') {
        this._time = time; this._color = color;
        this._chart = null; this._views = [];
      }
      attached({ chart }) {
        this._chart = chart;
        this._views = [new VerticalLinePaneView(this._time, this._color, chart)];
      }
      detached()       { this._views = []; }
      paneViews()      { return this._views; }
      updateAllViews() {}
    }

    document.querySelectorAll('.wick-row').forEach(row => {
      row.addEventListener('click', () => {
        const ticker   = row.dataset.ticker;
        const wickDate = row.dataset.wickDate;
        const existId  = 'wdrop-' + ticker;
        const exist = document.getElementById(existId);
        if (exist) { exist.remove(); row.classList.remove('active'); return; }
        document.querySelectorAll('.wick-drop').forEach(d => d.remove());
        document.querySelectorAll('.wick-row.active').forEach(r => r.classList.remove('active'));
        row.classList.add('active');
        const drop = document.createElement('tr');
        drop.id = existId; drop.className = 'wick-drop';
        drop.innerHTML = `<td colspan="8" style="background:#080a10;padding:16px 20px">
          <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:10px">
            <span style="color:#fff;font-weight:700;font-size:1rem">${ticker}</span>
            <span style="color:#555;font-size:.75rem" id="ws-${ticker}">Loading...</span>
          </div>
          <div id="wm-${ticker}" style="height:420px;background:#0a0c14;border-radius:6px"></div>
          <div id="wv-${ticker}" style="height:65px;background:#0a0c14;border-radius:6px;margin-top:3px"></div>
        </td>`;
        row.parentNode.insertBefore(drop, row.nextSibling);
        fetch('/api/us-chart/' + ticker)
          .then(r => r.json())
          .then(data => {
            if (data.error) { document.getElementById('ws-' + ticker).textContent = data.error; return; }
            document.getElementById('ws-' + ticker).textContent = data.bars + ' bars · ' + data.date_range;
            const chart = LightweightCharts.createChart(document.getElementById('wm-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: true },
              crosshair: { mode: LightweightCharts.CrosshairMode.Normal },
            });
            const candles = chart.addCandlestickSeries({
              upColor: '#22c55e', downColor: '#ef4444',
              borderUpColor: '#22c55e', borderDownColor: '#ef4444',
              wickUpColor: '#22c55e', wickDownColor: '#ef4444',
            });
            candles.setData(data.ohlcv);
            // Find closest actual trading day in the data to the wick date
            // (weekly wick date is a Friday that may not be in the daily series)
            const wickMs = new Date(wickDate).getTime();
            let snapDate = wickDate;
            let minDiff = Infinity;
            for (const bar of data.ohlcv) {
              const diff = Math.abs(new Date(bar.time).getTime() - wickMs);
              if (diff < minDiff) { minDiff = diff; snapDate = bar.time; }
            }
            candles.attachPrimitive(new VerticalLine(snapDate));
            const ema5  = chart.addLineSeries({ color: '#60a5fa', lineWidth: 1, title: 'EMA5' });
            const ema26 = chart.addLineSeries({ color: '#f59e0b', lineWidth: 1, title: 'EMA26' });
            ema5.setData(data.ema5); ema26.setData(data.ema26);
            const barCount = data.ohlcv.length;
            chart.timeScale().setVisibleLogicalRange({ from: 0, to: barCount + Math.round(barCount * 0.9) });
            chart.priceScale('right').applyOptions({ scaleMargins: { top: 0.12, bottom: 0.18 } });
            const vc = LightweightCharts.createChart(document.getElementById('wv-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: false },
            });
            const vs = vc.addHistogramSeries({ priceFormat: { type: 'volume' }, priceScaleId: '' });
            vs.priceScale().applyOptions({ scaleMargins: { top: 0.1, bottom: 0 } });
            vs.setData(data.volume); vc.timeScale().fitContent();
            chart.timeScale().subscribeVisibleLogicalRangeChange(r => vc.timeScale().setVisibleLogicalRange(r));
            vc.timeScale().subscribeVisibleLogicalRangeChange(r => chart.timeScale().setVisibleLogicalRange(r));
          })
          .catch(e => { document.getElementById('ws-' + ticker).textContent = 'Failed: ' + e; });
      });
    });
    </script>"""

    content = f"""
    <section style="margin-bottom:20px">
      <h2>Weekly Wick Scanner</h2>
      <p style="font-size:.88rem;color:#888;margin-bottom:16px">
        Finds weekly candles with a long lower wick (2×+ body) that have closed in the
        top 30% of range — and scores them by how many subsequent weeks have held above
        the wick low. Higher score = stronger signal.
      </p>
      <div class="btn-row" style="margin-bottom:8px">{run_btn}</div>
      <p class="note">{scan_info}</p>
    </section>

    {'<section><h2>Log</h2><pre>' + get_log().replace("<","&lt;") + '</pre></section>' if running and jname == "Wick Scan" else ''}

    <section>
      <style>
        .wick-table {{ width:100%; border-collapse:collapse; font-size:.92rem; }}
        .wick-table th {{ text-align:left; padding:10px 14px; color:#777; font-size:.78rem;
                         border-bottom:1px solid #2a2d3e; font-weight:500;
                         cursor:pointer; user-select:none; }}
        .wick-table th:hover {{ color:#aaa; }}
        .wick-table th.sort-asc::after  {{ content:' ▲'; font-size:.6rem; color:#60a5fa; }}
        .wick-table th.sort-desc::after {{ content:' ▼'; font-size:.6rem; color:#60a5fa; }}
        .wick-table td {{ padding:10px 14px; border-bottom:1px solid #151820; vertical-align:middle; }}
        .wick-table .wick-row:hover td {{ background:#1f2235; cursor:pointer; }}
        .wick-table .wick-row.active td {{ background:#1a2235; }}
        .wick-drop td {{ padding:0 !important; }}
        .wick-filter-btn {{ background:#1a1d2e; border:1px solid #2a2d3e; color:#888;
                            padding:6px 16px; border-radius:6px; cursor:pointer; font-size:.82rem; }}
        .wick-filter-btn.active {{ background:#1e3a5f; border-color:#3b82f6; color:#60a5fa; font-weight:600; }}
      </style>

      <div style="background:#0d0f1a;border:1px solid #1e2235;border-radius:8px;padding:14px 16px;margin-bottom:16px">
        <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:10px">
          <span style="color:#aaa;font-size:.82rem;font-weight:600;letter-spacing:.04em">TRADINGVIEW WATCHLIST</span>
          <button onclick="copyTVList()" id="tv-copy-btn"
            style="background:#1e3a5f;border:1px solid #3b82f6;color:#60a5fa;padding:5px 14px;
                   border-radius:5px;cursor:pointer;font-size:.78rem;font-weight:600">
            Copy
          </button>
        </div>
        <textarea id="tv-list" readonly rows="3"
          style="width:100%;background:#080a10;border:1px solid #1a1d2e;border-radius:5px;
                 color:#c7d2fe;font-size:.8rem;padding:8px 10px;resize:vertical;
                 font-family:monospace;box-sizing:border-box;line-height:1.6"></textarea>
        <p style="color:#444;font-size:.72rem;margin:6px 0 0">
          Paste directly into TradingView → Watchlist → Import. Updates when you switch Last Week / All.
        </p>
      </div>

      <div style="display:flex;align-items:center;gap:8px;margin-bottom:12px">
        <button class="wick-filter-btn active" id="wf-week" onclick="setWickFilter('week')">Last Week</button>
        <button class="wick-filter-btn"         id="wf-all"  onclick="setWickFilter('all')">All Signals</button>
        <span id="wick-count" style="color:#555;font-size:.78rem;margin-left:4px"></span>
      </div>
      <table class="wick-table">
        <thead><tr>
          <th onclick="sortWick(this)">Ticker</th>
          <th onclick="sortWick(this)">Wick Date</th>
          <th onclick="sortWick(this)" style="text-align:center">Score</th>
          <th onclick="sortWick(this)">Wick ×</th>
          <th onclick="sortWick(this)">Held</th>
          <th onclick="sortWick(this)">Close %</th>
          <th onclick="sortWick(this)">Current</th>
          <th onclick="sortWick(this)">Gain</th>
        </tr></thead>
        <tbody id="wick-tbody">
          {rows_html if rows_html else '<tr><td colspan="8" style="color:#555;padding:20px">No results yet — run the scan.</td></tr>'}
        </tbody>
      </table>
    </section>
    <script>
    function sortWick(th) {{
      const tbody = document.getElementById('wick-tbody');
      const idx = th.cellIndex;
      const asc = th.classList.contains('sort-desc');
      th.closest('thead').querySelectorAll('th').forEach(h => h.classList.remove('sort-asc','sort-desc'));
      th.classList.add(asc ? 'sort-asc' : 'sort-desc');
      const rows = Array.from(tbody.querySelectorAll('.wick-row'));
      rows.sort((a, b) => {{
        const av = a.cells[idx].textContent.trim();
        const bv = b.cells[idx].textContent.trim();
        const an = parseFloat(av.replace(/[^0-9.-]/g,'')), bn = parseFloat(bv.replace(/[^0-9.-]/g,''));
        const cmp = isNaN(an) ? av.localeCompare(bv) : an - bn;
        return asc ? cmp : -cmp;
      }});
      rows.forEach(r => tbody.appendChild(r));
    }}

    // Find the most recent wick date across all rows
    function getMostRecentWickDate() {{
      let latest = '';
      document.querySelectorAll('.wick-row').forEach(r => {{
        const d = r.dataset.wickDate || '';
        if (d > latest) latest = d;
      }});
      return latest;
    }}

    function setWickFilter(mode) {{
      document.getElementById('wf-week').classList.toggle('active', mode === 'week');
      document.getElementById('wf-all').classList.toggle('active',  mode === 'all');
      const latestDate = getMostRecentWickDate();
      let visible = 0;
      document.querySelectorAll('.wick-row').forEach(r => {{
        const show = (mode === 'all') || (r.dataset.wickDate === latestDate);
        r.style.display = show ? '' : 'none';
        if (show) visible++;
        // close any open drop if its row is hidden
        if (!show) {{
          const drop = document.getElementById('wdrop-' + r.dataset.ticker);
          if (drop) {{ drop.remove(); r.classList.remove('active'); }}
        }}
      }});
      document.getElementById('wick-count').textContent = visible + ' signal' + (visible !== 1 ? 's' : '');
      updateTVList();
    }}

    function updateTVList() {{
      const tickers = [];
      document.querySelectorAll('.wick-row').forEach(r => {{
        if (r.style.display !== 'none') tickers.push(r.dataset.ticker);
      }});
      document.getElementById('tv-list').value = tickers.join(',');
    }}

    function copyTVList() {{
      const ta = document.getElementById('tv-list');
      ta.select();
      ta.setSelectionRange(0, 99999);
      navigator.clipboard.writeText(ta.value).then(() => {{
        const btn = document.getElementById('tv-copy-btn');
        btn.textContent = 'Copied!';
        btn.style.background = '#14532d';
        btn.style.borderColor = '#22c55e';
        btn.style.color = '#4ade80';
        setTimeout(() => {{
          btn.textContent = 'Copy';
          btn.style.background = '#1e3a5f';
          btn.style.borderColor = '#3b82f6';
          btn.style.color = '#60a5fa';
        }}, 2000);
      }});
    }}

    // Default to last-week view on load
    setWickFilter('week');
    </script>
    {chart_js}"""

    return page_wrap('Wick Scanner', 'wick', content, auto_refresh=(running and jname == 'Wick Scan'))


# ─── Hammer Scanner ───────────────────────────────────────────────────────────

def _run_hammer_scan_job():
    global _job_running, _job_name
    with open(LOG_FILE, 'w') as f:
        f.write(f"=== Hammer Scan ===\nStarted: {datetime.now()}\n\n")
    try:
        run_hammer_scan(log_callback=lambda m: open(LOG_FILE, 'a').write(m))
    except Exception as e:
        with open(LOG_FILE, 'a') as f:
            f.write(f"\nERROR: {e}\n")
    finally:
        with _job_lock:
            _job_running = False
            _job_name    = ''


def start_hammer_scan():
    global _job_running, _job_name
    with _job_lock:
        if _job_running:
            return False
        _job_running = True
        _job_name    = 'Hammer Scan'
    threading.Thread(target=_run_hammer_scan_job, daemon=True).start()
    return True


@app.route('/run-hammer')
def run_hammer():
    if not is_admin():
        return redirect('/admin')
    start_hammer_scan()
    return redirect('/hammer')


@app.route('/hammer')
def hammer_page():
    if not is_admin():
        return redirect('/')

    with _job_lock:
        running = _job_running
        jname   = _job_name

    last = load_last_hammer_results()

    if running and jname == 'Hammer Scan':
        run_btn = '<span class="btn btn-off">⏳ Scanning…</span>'
    elif running:
        run_btn = '<span class="btn btn-off">Another job running</span>'
    else:
        run_btn = '<a href="/run-hammer" class="btn btn-blue">▶ Run Hammer Scan</a>'

    def score_color(s):
        if s >= 8:  return '#22c55e'
        if s >= 5:  return '#f59e0b'
        return '#555'

    rows_html = ''
    if last and last.get('results'):
        for r in last['results']:
            sc   = r['score']
            gc   = '#22c55e' if r['gain_pct'] >= 0 else '#ef4444'
            gs   = '+' if r['gain_pct'] >= 0 else ''
            held = r['days_held']
            bull_icon = '▲' if r.get('bullish') else '▽'
            bull_col  = '#22c55e' if r.get('bullish') else '#ef4444'
            vol_icon  = ' ⚡' if r.get('vol_surge') else ''
            rows_html += f"""
            <tr class="hammer-row" data-ticker="{r['ticker']}" data-hammer-date="{r['hammer_date']}">
              <td><strong style="color:#60a5fa;font-size:1rem">{r['ticker']}</strong></td>
              <td style="color:#aaa">{r['hammer_date']}</td>
              <td style="text-align:center">
                <span style="background:{score_color(sc)};color:#fff;padding:3px 10px;
                             border-radius:12px;font-weight:700;font-size:.85rem">{sc}</span>
              </td>
              <td style="color:#fff;font-weight:600">{r['wick_ratio']}×</td>
              <td style="color:#aaa">{held}d</td>
              <td style="color:#888">{r['close_pct']}%</td>
              <td style="color:{bull_col};font-weight:600">{bull_icon}{vol_icon}</td>
              <td style="color:#fff;font-weight:600">${r['current_price']:,.4f}</td>
              <td style="color:{gc};font-weight:700">{gs}{r['gain_pct']:.2f}%</td>
            </tr>"""

    scan_info = ''
    if last:
        scan_info = (f"Last scan: {last['scan_date']} &nbsp;·&nbsp; "
                     f"{last['total']} signals from {last['tickers_scanned']} tickers")

    chart_js = """
    <script src="https://unpkg.com/lightweight-charts@4.1.3/dist/lightweight-charts.standalone.production.js"></script>
    <script>
    // LightweightCharts v4 series primitive — paneViews() → renderer() → draw()
    class HammerLineRenderer {
      constructor(time, color, chart) {
        this._time = time; this._color = color; this._chart = chart;
      }
      draw(target) {
        const x = this._chart.timeScale().timeToCoordinate(this._time);
        if (x === null) return;
        target.useBitmapCoordinateSpace(scope => {
          const ctx = scope.context;
          const xb = Math.round(x * scope.horizontalPixelRatio);
          ctx.save();
          ctx.beginPath();
          ctx.moveTo(xb, 0);
          ctx.lineTo(xb, scope.bitmapSize.height);
          ctx.strokeStyle = this._color;
          ctx.lineWidth = Math.round(2 * scope.horizontalPixelRatio);
          ctx.setLineDash([6, 4]);
          ctx.stroke();
          ctx.restore();
        });
      }
    }
    class HammerLinePaneView {
      constructor(time, color, chart) {
        this._renderer = new HammerLineRenderer(time, color, chart);
      }
      renderer() { return this._renderer; }
      zOrder()   { return 'normal'; }
    }
    class HammerLine {
      constructor(time, color = '#f59e0b') {
        this._time = time; this._color = color;
        this._chart = null; this._views = [];
      }
      attached({ chart }) {
        this._chart = chart;
        this._views = [new HammerLinePaneView(this._time, this._color, chart)];
      }
      detached()       { this._views = []; }
      paneViews()      { return this._views; }
      updateAllViews() {}
    }

    document.querySelectorAll('.hammer-row').forEach(row => {
      row.addEventListener('click', () => {
        const ticker      = row.dataset.ticker;
        const hammerDate  = row.dataset.hammerDate;
        const existId     = 'hdrop-' + ticker;
        const exist = document.getElementById(existId);
        if (exist) { exist.remove(); row.classList.remove('active'); return; }
        document.querySelectorAll('.hammer-drop').forEach(d => d.remove());
        document.querySelectorAll('.hammer-row.active').forEach(r => r.classList.remove('active'));
        row.classList.add('active');
        const drop = document.createElement('tr');
        drop.id = existId; drop.className = 'hammer-drop';
        drop.innerHTML = `<td colspan="9" style="background:#080a10;padding:16px 20px">
          <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:10px">
            <span style="color:#fff;font-weight:700;font-size:1rem">${ticker}</span>
            <span style="color:#555;font-size:.75rem" id="hs-${ticker}">Loading...</span>
          </div>
          <div id="hm-${ticker}" style="height:420px;background:#0a0c14;border-radius:6px"></div>
          <div id="hv-${ticker}" style="height:65px;background:#0a0c14;border-radius:6px;margin-top:3px"></div>
        </td>`;
        row.parentNode.insertBefore(drop, row.nextSibling);
        fetch('/api/us-chart/' + ticker)
          .then(r => r.json())
          .then(data => {
            if (data.error) { document.getElementById('hs-' + ticker).textContent = data.error; return; }
            document.getElementById('hs-' + ticker).textContent = data.bars + ' bars · ' + data.date_range;
            const chart = LightweightCharts.createChart(document.getElementById('hm-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: true },
              crosshair: { mode: LightweightCharts.CrosshairMode.Normal },
            });
            const candles = chart.addCandlestickSeries({
              upColor: '#22c55e', downColor: '#ef4444',
              borderUpColor: '#22c55e', borderDownColor: '#ef4444',
              wickUpColor: '#22c55e', wickDownColor: '#ef4444',
            });
            candles.setData(data.ohlcv);
            // Snap to the exact hammer date (daily data — should match exactly)
            const hammerMs = new Date(hammerDate).getTime();
            let snapDate = hammerDate;
            let minDiff = Infinity;
            for (const bar of data.ohlcv) {
              const diff = Math.abs(new Date(bar.time).getTime() - hammerMs);
              if (diff < minDiff) { minDiff = diff; snapDate = bar.time; }
            }
            candles.attachPrimitive(new HammerLine(snapDate));
            const ema5  = chart.addLineSeries({ color: '#60a5fa', lineWidth: 1, title: 'EMA5' });
            const ema26 = chart.addLineSeries({ color: '#f59e0b', lineWidth: 1, title: 'EMA26' });
            ema5.setData(data.ema5); ema26.setData(data.ema26);
            const barCount = data.ohlcv.length;
            chart.timeScale().setVisibleLogicalRange({ from: Math.max(0, barCount - 120), to: barCount + 5 });
            chart.priceScale('right').applyOptions({ scaleMargins: { top: 0.12, bottom: 0.18 } });
            const vc = LightweightCharts.createChart(document.getElementById('hv-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: false },
            });
            const vs = vc.addHistogramSeries({ priceFormat: { type: 'volume' }, priceScaleId: '' });
            vs.priceScale().applyOptions({ scaleMargins: { top: 0.1, bottom: 0 } });
            vs.setData(data.volume); vc.timeScale().fitContent();
            chart.timeScale().subscribeVisibleLogicalRangeChange(r => vc.timeScale().setVisibleLogicalRange(r));
            vc.timeScale().subscribeVisibleLogicalRangeChange(r => chart.timeScale().setVisibleLogicalRange(r));
          })
          .catch(e => { document.getElementById('hs-' + ticker).textContent = 'Failed: ' + e; });
      });
    });
    </script>"""

    content = f"""
    <section style="margin-bottom:20px">
      <h2>Daily Hammer Scanner</h2>
      <p style="font-size:.88rem;color:#888;margin-bottom:16px">
        Finds daily hammer candles — small body near the top of range with a long lower wick
        (2×+ body) showing buyers rejected the lows. Scored by wick strength, close position,
        bullish body, volume surge, and how many days the hammer low has held.
      </p>
      <div class="btn-row" style="margin-bottom:8px">{run_btn}</div>
      <p class="note">{scan_info}</p>
    </section>

    {'<section><h2>Log</h2><pre>' + get_log().replace("<","&lt;") + '</pre></section>' if running and jname == "Hammer Scan" else ''}

    <section>
      <style>
        .hammer-table {{ width:100%; border-collapse:collapse; font-size:.92rem; }}
        .hammer-table th {{ text-align:left; padding:10px 14px; color:#777; font-size:.78rem;
                           border-bottom:1px solid #2a2d3e; font-weight:500;
                           cursor:pointer; user-select:none; }}
        .hammer-table th:hover {{ color:#aaa; }}
        .hammer-table th.sort-asc::after  {{ content:' ▲'; font-size:.6rem; color:#60a5fa; }}
        .hammer-table th.sort-desc::after {{ content:' ▼'; font-size:.6rem; color:#60a5fa; }}
        .hammer-table td {{ padding:10px 14px; border-bottom:1px solid #151820; vertical-align:middle; }}
        .hammer-table .hammer-row:hover td {{ background:#1f2235; cursor:pointer; }}
        .hammer-table .hammer-row.active td {{ background:#1a2235; }}
        .hammer-drop td {{ padding:0 !important; }}
        .hammer-filter-btn {{ background:#1a1d2e; border:1px solid #2a2d3e; color:#888;
                              padding:6px 16px; border-radius:6px; cursor:pointer; font-size:.82rem; }}
        .hammer-filter-btn.active {{ background:#1e3a5f; border-color:#3b82f6; color:#60a5fa; font-weight:600; }}
      </style>

      <div style="background:#0d0f1a;border:1px solid #1e2235;border-radius:8px;padding:14px 16px;margin-bottom:16px">
        <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:10px">
          <span style="color:#aaa;font-size:.82rem;font-weight:600;letter-spacing:.04em">TRADINGVIEW WATCHLIST</span>
          <button onclick="copyHammerList()" id="htv-copy-btn"
            style="background:#1e3a5f;border:1px solid #3b82f6;color:#60a5fa;padding:5px 14px;
                   border-radius:5px;cursor:pointer;font-size:.78rem;font-weight:600">
            Copy
          </button>
        </div>
        <textarea id="htv-list" readonly rows="3"
          style="width:100%;background:#080a10;border:1px solid #1a1d2e;border-radius:5px;
                 color:#c7d2fe;font-size:.8rem;padding:8px 10px;resize:vertical;
                 font-family:monospace;box-sizing:border-box;line-height:1.6"></textarea>
        <p style="color:#444;font-size:.72rem;margin:6px 0 0">
          Paste directly into TradingView → Watchlist → Import. Updates when you switch Today / All.
        </p>
      </div>

      <div style="display:flex;align-items:center;gap:8px;margin-bottom:12px">
        <button class="hammer-filter-btn active" id="hf-today" onclick="setHammerFilter('today')">Today</button>
        <button class="hammer-filter-btn"         id="hf-all"   onclick="setHammerFilter('all')">All Signals</button>
        <span id="hammer-count" style="color:#555;font-size:.78rem;margin-left:4px"></span>
      </div>
      <table class="hammer-table">
        <thead><tr>
          <th onclick="sortHammer(this)">Ticker</th>
          <th onclick="sortHammer(this)">Date</th>
          <th onclick="sortHammer(this)" style="text-align:center">Score</th>
          <th onclick="sortHammer(this)">Wick ×</th>
          <th onclick="sortHammer(this)">Held</th>
          <th onclick="sortHammer(this)">Close %</th>
          <th onclick="sortHammer(this)">Body</th>
          <th onclick="sortHammer(this)">Current</th>
          <th onclick="sortHammer(this)">Gain</th>
        </tr></thead>
        <tbody id="hammer-tbody">
          {rows_html if rows_html else '<tr><td colspan="9" style="color:#555;padding:20px">No results yet — run the scan.</td></tr>'}
        </tbody>
      </table>
    </section>
    <script>
    function sortHammer(th) {{
      const tbody = document.getElementById('hammer-tbody');
      const idx = th.cellIndex;
      const asc = th.classList.contains('sort-desc');
      th.closest('thead').querySelectorAll('th').forEach(h => h.classList.remove('sort-asc','sort-desc'));
      th.classList.add(asc ? 'sort-asc' : 'sort-desc');
      const rows = Array.from(tbody.querySelectorAll('.hammer-row'));
      rows.sort((a, b) => {{
        const av = a.cells[idx].textContent.trim();
        const bv = b.cells[idx].textContent.trim();
        const an = parseFloat(av.replace(/[^0-9.-]/g,'')), bn = parseFloat(bv.replace(/[^0-9.-]/g,''));
        const cmp = isNaN(an) ? av.localeCompare(bv) : an - bn;
        return asc ? cmp : -cmp;
      }});
      rows.forEach(r => tbody.appendChild(r));
    }}

    function getMostRecentHammerDate() {{
      let latest = '';
      document.querySelectorAll('.hammer-row').forEach(r => {{
        const d = r.dataset.hammerDate || '';
        if (d > latest) latest = d;
      }});
      return latest;
    }}

    function setHammerFilter(mode) {{
      document.getElementById('hf-today').classList.toggle('active', mode === 'today');
      document.getElementById('hf-all').classList.toggle('active',   mode === 'all');
      const latestDate = getMostRecentHammerDate();
      let visible = 0;
      document.querySelectorAll('.hammer-row').forEach(r => {{
        const show = (mode === 'all') || (r.dataset.hammerDate === latestDate);
        r.style.display = show ? '' : 'none';
        if (show) visible++;
        if (!show) {{
          const drop = document.getElementById('hdrop-' + r.dataset.ticker);
          if (drop) {{ drop.remove(); r.classList.remove('active'); }}
        }}
      }});
      document.getElementById('hammer-count').textContent = visible + ' signal' + (visible !== 1 ? 's' : '');
      updateHammerList();
    }}

    function updateHammerList() {{
      const tickers = [];
      document.querySelectorAll('.hammer-row').forEach(r => {{
        if (r.style.display !== 'none') tickers.push(r.dataset.ticker);
      }});
      document.getElementById('htv-list').value = tickers.join(',');
    }}

    function copyHammerList() {{
      const ta = document.getElementById('htv-list');
      ta.select();
      ta.setSelectionRange(0, 99999);
      navigator.clipboard.writeText(ta.value).then(() => {{
        const btn = document.getElementById('htv-copy-btn');
        btn.textContent = 'Copied!';
        btn.style.background = '#14532d';
        btn.style.borderColor = '#22c55e';
        btn.style.color = '#4ade80';
        setTimeout(() => {{
          btn.textContent = 'Copy';
          btn.style.background = '#1e3a5f';
          btn.style.borderColor = '#3b82f6';
          btn.style.color = '#60a5fa';
        }}, 2000);
      }});
    }}

    setHammerFilter('today');
    </script>
    {chart_js}"""

    return page_wrap('Hammer Scanner', 'hammer', content, auto_refresh=(running and jname == 'Hammer Scan'))


# ─── Gap Down Scanner ───────────────────────────────────────────────────────

def _run_gapdown_scan_job():
    global _job_running, _job_name
    with open(LOG_FILE, 'w') as f:
        f.write(f"=== Gap Down Scan ===\nStarted: {datetime.now()}\n\n")
    try:
        run_gapdown_scan(log_callback=lambda m: open(LOG_FILE, 'a').write(m))
    except Exception as e:
        with open(LOG_FILE, 'a') as f:
            f.write(f"\nERROR: {e}\n")
    finally:
        with _job_lock:
            _job_running = False
            _job_name    = ''


def start_gapdown_scan():
    global _job_running, _job_name
    with _job_lock:
        if _job_running:
            return False
        _job_running = True
        _job_name    = 'Gap Down Scan'
    threading.Thread(target=_run_gapdown_scan_job, daemon=True).start()
    return True


@app.route('/run-gapdown')
def run_gapdown():
    if not is_admin():
        return redirect('/admin')
    start_gapdown_scan()
    return redirect('/gapdown')


@app.route('/gapdown')
def gapdown_page():
    if not is_admin():
        return redirect('/')

    with _job_lock:
        running = _job_running
        jname   = _job_name

    last = load_last_gapdown_results()

    if running and jname == 'Gap Down Scan':
        run_btn = '<span class="btn btn-off">⏳ Scanning…</span>'
    elif running:
        run_btn = '<span class="btn btn-off">Another job running</span>'
    else:
        run_btn = '<a href="/run-gapdown" class="btn btn-blue">▶ Run Gap Down Scan</a>'

    def score_color(s):
        if s >= 8:  return '#22c55e'
        if s >= 5:  return '#f59e0b'
        return '#555'

    rows_html = ''
    if last and last.get('results'):
        for r in last['results']:
            sc   = r['score']
            gc   = '#22c55e' if r['gain_pct'] >= 0 else '#ef4444'
            gs   = '+' if r['gain_pct'] >= 0 else ''
            held = r['days_held']
            rec_icon = '▲' if r.get('recovered_intraday') else '▽'
            rec_col  = '#22c55e' if r.get('recovered_intraday') else '#ef4444'
            vol_icon = ' ⚡' if r.get('vol_surge') else ''
            rows_html += f"""
            <tr class="gapdown-row" data-ticker="{r['ticker']}" data-gap-date="{r['gap_date']}">
              <td><strong style="color:#60a5fa;font-size:1rem">{r['ticker']}</strong></td>
              <td style="color:#aaa">{r['gap_date']}</td>
              <td style="text-align:center">
                <span style="background:{score_color(sc)};color:#fff;padding:3px 10px;
                             border-radius:12px;font-weight:700;font-size:.85rem">{sc}</span>
              </td>
              <td style="color:#ef4444;font-weight:600">{r['gap_pct']}%</td>
              <td style="color:#aaa">{held}d</td>
              <td style="color:#888">{r['close_pct']}%</td>
              <td style="color:#60a5fa">{r['fill_pct']}%</td>
              <td style="color:{rec_col};font-weight:600">{rec_icon}{vol_icon}</td>
              <td style="color:#fff;font-weight:600">${r['current_price']:,.4f}</td>
              <td style="color:{gc};font-weight:700">{gs}{r['gain_pct']:.2f}%</td>
            </tr>"""

    scan_info = ''
    if last:
        scan_info = (f"Last scan: {last['scan_date']} &nbsp;·&nbsp; "
                     f"{last['total']} signals from {last['tickers_scanned']} tickers")

    chart_js = """
    <script src="https://unpkg.com/lightweight-charts@4.1.3/dist/lightweight-charts.standalone.production.js"></script>
    <script>
    class GapLineRenderer {
      constructor(time, color, chart) {
        this._time = time; this._color = color; this._chart = chart;
      }
      draw(target) {
        const x = this._chart.timeScale().timeToCoordinate(this._time);
        if (x === null) return;
        target.useBitmapCoordinateSpace(scope => {
          const ctx = scope.context;
          const xb = Math.round(x * scope.horizontalPixelRatio);
          ctx.save();
          ctx.beginPath();
          ctx.moveTo(xb, 0);
          ctx.lineTo(xb, scope.bitmapSize.height);
          ctx.strokeStyle = this._color;
          ctx.lineWidth = Math.round(2 * scope.horizontalPixelRatio);
          ctx.setLineDash([6, 4]);
          ctx.stroke();
          ctx.restore();
        });
      }
    }
    class GapLinePaneView {
      constructor(time, color, chart) {
        this._renderer = new GapLineRenderer(time, color, chart);
      }
      renderer() { return this._renderer; }
      zOrder()   { return 'normal'; }
    }
    class GapLine {
      constructor(time, color = '#ef4444') {
        this._time = time; this._color = color;
        this._chart = null; this._views = [];
      }
      attached({ chart }) {
        this._chart = chart;
        this._views = [new GapLinePaneView(this._time, this._color, chart)];
      }
      detached()       { this._views = []; }
      paneViews()      { return this._views; }
      updateAllViews() {}
    }

    document.querySelectorAll('.gapdown-row').forEach(row => {
      row.addEventListener('click', () => {
        const ticker  = row.dataset.ticker;
        const gapDate = row.dataset.gapDate;
        const existId = 'gdrop-' + ticker;
        const exist = document.getElementById(existId);
        if (exist) { exist.remove(); row.classList.remove('active'); return; }
        document.querySelectorAll('.gapdown-drop').forEach(d => d.remove());
        document.querySelectorAll('.gapdown-row.active').forEach(r => r.classList.remove('active'));
        row.classList.add('active');
        const drop = document.createElement('tr');
        drop.id = existId; drop.className = 'gapdown-drop';
        drop.innerHTML = `<td colspan="10" style="background:#080a10;padding:16px 20px">
          <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:10px">
            <span style="color:#fff;font-weight:700;font-size:1rem">${ticker}</span>
            <span style="color:#555;font-size:.75rem" id="gs-${ticker}">Loading...</span>
          </div>
          <div id="gm-${ticker}" style="height:420px;background:#0a0c14;border-radius:6px"></div>
          <div id="gv-${ticker}" style="height:65px;background:#0a0c14;border-radius:6px;margin-top:3px"></div>
        </td>`;
        row.parentNode.insertBefore(drop, row.nextSibling);
        fetch('/api/us-chart/' + ticker)
          .then(r => r.json())
          .then(data => {
            if (data.error) { document.getElementById('gs-' + ticker).textContent = data.error; return; }
            document.getElementById('gs-' + ticker).textContent = data.bars + ' bars · ' + data.date_range;
            const chart = LightweightCharts.createChart(document.getElementById('gm-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: true },
              crosshair: { mode: LightweightCharts.CrosshairMode.Normal },
            });
            const candles = chart.addCandlestickSeries({
              upColor: '#22c55e', downColor: '#ef4444',
              borderUpColor: '#22c55e', borderDownColor: '#ef4444',
              wickUpColor: '#22c55e', wickDownColor: '#ef4444',
            });
            candles.setData(data.ohlcv);
            const gapMs = new Date(gapDate).getTime();
            let snapDate = gapDate;
            let minDiff = Infinity;
            for (const bar of data.ohlcv) {
              const diff = Math.abs(new Date(bar.time).getTime() - gapMs);
              if (diff < minDiff) { minDiff = diff; snapDate = bar.time; }
            }
            candles.attachPrimitive(new GapLine(snapDate));
            const ema5  = chart.addLineSeries({ color: '#60a5fa', lineWidth: 1, title: 'EMA5' });
            const ema26 = chart.addLineSeries({ color: '#f59e0b', lineWidth: 1, title: 'EMA26' });
            ema5.setData(data.ema5); ema26.setData(data.ema26);
            const barCount = data.ohlcv.length;
            chart.timeScale().setVisibleLogicalRange({ from: Math.max(0, barCount - 120), to: barCount + 5 });
            chart.priceScale('right').applyOptions({ scaleMargins: { top: 0.12, bottom: 0.18 } });
            const vc = LightweightCharts.createChart(document.getElementById('gv-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: false },
            });
            const vs = vc.addHistogramSeries({ priceFormat: { type: 'volume' }, priceScaleId: '' });
            vs.priceScale().applyOptions({ scaleMargins: { top: 0.1, bottom: 0 } });
            vs.setData(data.volume); vc.timeScale().fitContent();
            chart.timeScale().subscribeVisibleLogicalRangeChange(r => vc.timeScale().setVisibleLogicalRange(r));
            vc.timeScale().subscribeVisibleLogicalRangeChange(r => chart.timeScale().setVisibleLogicalRange(r));
          })
          .catch(e => { document.getElementById('gs-' + ticker).textContent = 'Failed: ' + e; });
      });
    });
    </script>"""

    content = f"""
    <section style="margin-bottom:20px">
      <h2>Gap Down Scanner</h2>
      <p style="font-size:.88rem;color:#888;margin-bottom:16px">
        Finds stocks that gapped down 10%+ (open vs. prior close) on above-average volume —
        potential mean-reversion / gap-fill candidates. Unlike the compression scanners, these
        are usually news-driven, so check the "Held" column (days without a new low since the
        gap) before treating this as a clean setup.
      </p>
      <div class="btn-row" style="margin-bottom:8px">{run_btn}</div>
      <p class="note">{scan_info}</p>
    </section>

    {'<section><h2>Log</h2><pre>' + get_log().replace("<","&lt;") + '</pre></section>' if running and jname == "Gap Down Scan" else ''}

    <section>
      <style>
        .gapdown-table {{ width:100%; border-collapse:collapse; font-size:.92rem; }}
        .gapdown-table th {{ text-align:left; padding:10px 14px; color:#777; font-size:.78rem;
                           border-bottom:1px solid #2a2d3e; font-weight:500;
                           cursor:pointer; user-select:none; }}
        .gapdown-table th:hover {{ color:#aaa; }}
        .gapdown-table th.sort-asc::after  {{ content:' ▲'; font-size:.6rem; color:#60a5fa; }}
        .gapdown-table th.sort-desc::after {{ content:' ▼'; font-size:.6rem; color:#60a5fa; }}
        .gapdown-table td {{ padding:10px 14px; border-bottom:1px solid #151820; vertical-align:middle; }}
        .gapdown-table .gapdown-row:hover td {{ background:#1f2235; cursor:pointer; }}
        .gapdown-table .gapdown-row.active td {{ background:#1a2235; }}
        .gapdown-drop td {{ padding:0 !important; }}
        .gapdown-filter-btn {{ background:#1a1d2e; border:1px solid #2a2d3e; color:#888;
                              padding:6px 16px; border-radius:6px; cursor:pointer; font-size:.82rem; }}
        .gapdown-filter-btn.active {{ background:#1e3a5f; border-color:#3b82f6; color:#60a5fa; font-weight:600; }}
      </style>

      <div style="background:#0d0f1a;border:1px solid #1e2235;border-radius:8px;padding:14px 16px;margin-bottom:16px">
        <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:10px">
          <span style="color:#aaa;font-size:.82rem;font-weight:600;letter-spacing:.04em">TRADINGVIEW WATCHLIST</span>
          <button onclick="copyGapdownList()" id="gtv-copy-btn"
            style="background:#1e3a5f;border:1px solid #3b82f6;color:#60a5fa;padding:5px 14px;
                   border-radius:5px;cursor:pointer;font-size:.78rem;font-weight:600">
            Copy
          </button>
        </div>
        <textarea id="gtv-list" readonly rows="3"
          style="width:100%;background:#080a10;border:1px solid #1a1d2e;border-radius:5px;
                 color:#c7d2fe;font-size:.8rem;padding:8px 10px;resize:vertical;
                 font-family:monospace;box-sizing:border-box;line-height:1.6"></textarea>
        <p style="color:#444;font-size:.72rem;margin:6px 0 0">
          Paste directly into TradingView → Watchlist → Import. Updates when you switch Today / All.
        </p>
      </div>

      <div style="display:flex;align-items:center;gap:8px;margin-bottom:12px">
        <button class="gapdown-filter-btn active" id="gf-today" onclick="setGapdownFilter('today')">Today</button>
        <button class="gapdown-filter-btn"         id="gf-all"   onclick="setGapdownFilter('all')">All Signals</button>
        <span id="gapdown-count" style="color:#555;font-size:.78rem;margin-left:4px"></span>
      </div>
      <table class="gapdown-table">
        <thead><tr>
          <th onclick="sortGapdown(this)">Ticker</th>
          <th onclick="sortGapdown(this)">Date</th>
          <th onclick="sortGapdown(this)" style="text-align:center">Score</th>
          <th onclick="sortGapdown(this)">Gap %</th>
          <th onclick="sortGapdown(this)">Held</th>
          <th onclick="sortGapdown(this)">Close %</th>
          <th onclick="sortGapdown(this)">Fill %</th>
          <th onclick="sortGapdown(this)">Flags</th>
          <th onclick="sortGapdown(this)">Current</th>
          <th onclick="sortGapdown(this)">Gain</th>
        </tr></thead>
        <tbody id="gapdown-tbody">
          {rows_html if rows_html else '<tr><td colspan="10" style="color:#555;padding:20px">No results yet — run the scan.</td></tr>'}
        </tbody>
      </table>
    </section>
    <script>
    function sortGapdown(th) {{
      const tbody = document.getElementById('gapdown-tbody');
      const idx = th.cellIndex;
      const asc = th.classList.contains('sort-desc');
      th.closest('thead').querySelectorAll('th').forEach(h => h.classList.remove('sort-asc','sort-desc'));
      th.classList.add(asc ? 'sort-asc' : 'sort-desc');
      const rows = Array.from(tbody.querySelectorAll('.gapdown-row'));
      rows.sort((a, b) => {{
        const av = a.cells[idx].textContent.trim();
        const bv = b.cells[idx].textContent.trim();
        const an = parseFloat(av.replace(/[^0-9.-]/g,'')), bn = parseFloat(bv.replace(/[^0-9.-]/g,''));
        const cmp = isNaN(an) ? av.localeCompare(bv) : an - bn;
        return asc ? cmp : -cmp;
      }});
      rows.forEach(r => tbody.appendChild(r));
    }}

    function getMostRecentGapdownDate() {{
      let latest = '';
      document.querySelectorAll('.gapdown-row').forEach(r => {{
        const d = r.dataset.gapDate || '';
        if (d > latest) latest = d;
      }});
      return latest;
    }}

    function setGapdownFilter(mode) {{
      document.getElementById('gf-today').classList.toggle('active', mode === 'today');
      document.getElementById('gf-all').classList.toggle('active',   mode === 'all');
      const latestDate = getMostRecentGapdownDate();
      let visible = 0;
      document.querySelectorAll('.gapdown-row').forEach(r => {{
        const show = (mode === 'all') || (r.dataset.gapDate === latestDate);
        r.style.display = show ? '' : 'none';
        if (show) visible++;
        if (!show) {{
          const drop = document.getElementById('gdrop-' + r.dataset.ticker);
          if (drop) {{ drop.remove(); r.classList.remove('active'); }}
        }}
      }});
      document.getElementById('gapdown-count').textContent = visible + ' signal' + (visible !== 1 ? 's' : '');
      updateGapdownList();
    }}

    function updateGapdownList() {{
      const tickers = [];
      document.querySelectorAll('.gapdown-row').forEach(r => {{
        if (r.style.display !== 'none') tickers.push(r.dataset.ticker);
      }});
      document.getElementById('gtv-list').value = tickers.join(',');
    }}

    function copyGapdownList() {{
      const ta = document.getElementById('gtv-list');
      ta.select();
      ta.setSelectionRange(0, 99999);
      navigator.clipboard.writeText(ta.value).then(() => {{
        const btn = document.getElementById('gtv-copy-btn');
        btn.textContent = 'Copied!';
        btn.style.background = '#14532d';
        btn.style.borderColor = '#22c55e';
        btn.style.color = '#4ade80';
        setTimeout(() => {{
          btn.textContent = 'Copy';
          btn.style.background = '#1e3a5f';
          btn.style.borderColor = '#3b82f6';
          btn.style.color = '#60a5fa';
        }}, 2000);
      }});
    }}

    setGapdownFilter('today');
    </script>
    {chart_js}"""

    return page_wrap('Gap Down Scanner', 'gapdown', content, auto_refresh=(running and jname == 'Gap Down Scan'))


# ─── Marubozu Scanner ────────────────────────────────────────────────────────

def _run_marubozu_scan_job():
    global _job_running, _job_name
    with open(LOG_FILE, 'w') as f:
        f.write(f"=== Marubozu Scan ===\nStarted: {datetime.now()}\n\n")
    try:
        run_marubozu_scan(log_callback=lambda m: open(LOG_FILE, 'a').write(m))
    except Exception as e:
        with open(LOG_FILE, 'a') as f:
            f.write(f"\nERROR: {e}\n")
    finally:
        with _job_lock:
            _job_running = False
            _job_name    = ''


def start_marubozu_scan():
    global _job_running, _job_name
    with _job_lock:
        if _job_running:
            return False
        _job_running = True
        _job_name    = 'Marubozu Scan'
    threading.Thread(target=_run_marubozu_scan_job, daemon=True).start()
    return True


@app.route('/run-marubozu')
def run_marubozu():
    if not is_admin():
        return redirect('/admin')
    start_marubozu_scan()
    return redirect('/marubozu')


@app.route('/marubozu')
def marubozu_page():
    if not is_admin():
        return redirect('/')

    with _job_lock:
        running = _job_running
        jname   = _job_name

    last = load_last_marubozu_results()

    if running and jname == 'Marubozu Scan':
        run_btn = '<span class="btn btn-off">⏳ Scanning…</span>'
    elif running:
        run_btn = '<span class="btn btn-off">Another job running</span>'
    else:
        run_btn = '<a href="/run-marubozu" class="btn btn-blue">▶ Run Marubozu Scan</a>'

    def score_color(s):
        if s >= 7:  return '#22c55e'
        if s >= 4:  return '#f59e0b'
        return '#555'

    rows_html = ''
    if last and last.get('results'):
        for r in last['results']:
            sc  = r['score']
            gc  = '#22c55e' if r['gain_pct'] >= 0 else '#ef4444'
            gs  = '+' if r['gain_pct'] >= 0 else ''
            vol_icon = ' ⚡' if r.get('vol_surge') else ''
            rows_html += f"""
            <tr class="maru-row" data-ticker="{r['ticker']}" data-maru-date="{r['marubozu_date']}">
              <td><strong style="color:#60a5fa;font-size:1rem">{r['ticker']}</strong></td>
              <td style="color:#aaa">{r['marubozu_date']}</td>
              <td style="text-align:center">
                <span style="background:{score_color(sc)};color:#fff;padding:3px 10px;
                             border-radius:12px;font-weight:700;font-size:.85rem">{sc}</span>
              </td>
              <td style="color:#fff;font-weight:600">{r['body_pct']}%</td>
              <td style="color:#888">{r['upper_wick_pct']}%</td>
              <td style="color:#888">{r['lower_wick_pct']}%</td>
              <td style="color:#aaa">{r['days_held']}d</td>
              <td style="color:#555">{vol_icon if vol_icon else '—'}</td>
              <td style="color:#fff;font-weight:600">${r['current_price']:,.4f}</td>
              <td style="color:{gc};font-weight:700">{gs}{r['gain_pct']:.2f}%</td>
            </tr>"""

    scan_info = ''
    if last:
        scan_info = (f"Last scan: {last['scan_date']} &nbsp;·&nbsp; "
                     f"{last['total']} signals from {last['tickers_scanned']} tickers")

    chart_js = """
    <script src="https://unpkg.com/lightweight-charts@4.1.3/dist/lightweight-charts.standalone.production.js"></script>
    <script>
    // LightweightCharts v4 vertical line primitive — paneViews() → renderer() → draw()
    class MaruLineRenderer {
      constructor(time, color, chart) {
        this._time = time; this._color = color; this._chart = chart;
      }
      draw(target) {
        const x = this._chart.timeScale().timeToCoordinate(this._time);
        if (x === null) return;
        target.useBitmapCoordinateSpace(scope => {
          const ctx = scope.context;
          const xb = Math.round(x * scope.horizontalPixelRatio);
          ctx.save();
          ctx.beginPath();
          ctx.moveTo(xb, 0);
          ctx.lineTo(xb, scope.bitmapSize.height);
          ctx.strokeStyle = this._color;
          ctx.lineWidth = Math.round(2 * scope.horizontalPixelRatio);
          ctx.setLineDash([6, 4]);
          ctx.stroke();
          ctx.restore();
        });
      }
    }
    class MaruLinePaneView {
      constructor(time, color, chart) {
        this._renderer = new MaruLineRenderer(time, color, chart);
      }
      renderer() { return this._renderer; }
      zOrder()   { return 'normal'; }
    }
    class MaruLine {
      constructor(time, color = '#22c55e') {
        this._time = time; this._color = color;
        this._chart = null; this._views = [];
      }
      attached({ chart }) {
        this._chart = chart;
        this._views = [new MaruLinePaneView(this._time, this._color, chart)];
      }
      detached()       { this._views = []; }
      paneViews()      { return this._views; }
      updateAllViews() {}
    }

    document.querySelectorAll('.maru-row').forEach(row => {
      row.addEventListener('click', () => {
        const ticker   = row.dataset.ticker;
        const maruDate = row.dataset.maruDate;
        const existId  = 'mdrop-' + ticker;
        const exist = document.getElementById(existId);
        if (exist) { exist.remove(); row.classList.remove('active'); return; }
        document.querySelectorAll('.maru-drop').forEach(d => d.remove());
        document.querySelectorAll('.maru-row.active').forEach(r => r.classList.remove('active'));
        row.classList.add('active');
        const drop = document.createElement('tr');
        drop.id = existId; drop.className = 'maru-drop';
        drop.innerHTML = `<td colspan="10" style="background:#080a10;padding:16px 20px">
          <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:10px">
            <span style="color:#fff;font-weight:700;font-size:1rem">${ticker}</span>
            <span style="color:#555;font-size:.75rem" id="ms-${ticker}">Loading...</span>
          </div>
          <div id="mm-${ticker}" style="height:420px;background:#0a0c14;border-radius:6px"></div>
          <div id="mv-${ticker}" style="height:65px;background:#0a0c14;border-radius:6px;margin-top:3px"></div>
        </td>`;
        row.parentNode.insertBefore(drop, row.nextSibling);
        fetch('/api/us-chart/' + ticker)
          .then(r => r.json())
          .then(data => {
            if (data.error) { document.getElementById('ms-' + ticker).textContent = data.error; return; }
            document.getElementById('ms-' + ticker).textContent = data.bars + ' bars · ' + data.date_range;
            const chart = LightweightCharts.createChart(document.getElementById('mm-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: true },
              crosshair: { mode: LightweightCharts.CrosshairMode.Normal },
            });
            const candles = chart.addCandlestickSeries({
              upColor: '#22c55e', downColor: '#ef4444',
              borderUpColor: '#22c55e', borderDownColor: '#ef4444',
              wickUpColor: '#22c55e', wickDownColor: '#ef4444',
            });
            candles.setData(data.ohlcv);
            // Snap the marker to the closest bar to the Marubozu date
            const maruMs = new Date(maruDate).getTime();
            let snapDate = maruDate;
            let minDiff = Infinity;
            for (const bar of data.ohlcv) {
              const diff = Math.abs(new Date(bar.time).getTime() - maruMs);
              if (diff < minDiff) { minDiff = diff; snapDate = bar.time; }
            }
            candles.attachPrimitive(new MaruLine(snapDate));
            const ema5  = chart.addLineSeries({ color: '#60a5fa', lineWidth: 1, title: 'EMA5' });
            const ema26 = chart.addLineSeries({ color: '#f59e0b', lineWidth: 1, title: 'EMA26' });
            ema5.setData(data.ema5); ema26.setData(data.ema26);
            const barCount = data.ohlcv.length;
            chart.timeScale().setVisibleLogicalRange({ from: Math.max(0, barCount - 120), to: barCount + 5 });
            chart.priceScale('right').applyOptions({ scaleMargins: { top: 0.12, bottom: 0.18 } });
            const vc = LightweightCharts.createChart(document.getElementById('mv-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: false },
            });
            const vs = vc.addHistogramSeries({ priceFormat: { type: 'volume' }, priceScaleId: '' });
            vs.priceScale().applyOptions({ scaleMargins: { top: 0.1, bottom: 0 } });
            vs.setData(data.volume); vc.timeScale().fitContent();
            chart.timeScale().subscribeVisibleLogicalRangeChange(r => vc.timeScale().setVisibleLogicalRange(r));
            vc.timeScale().subscribeVisibleLogicalRangeChange(r => chart.timeScale().setVisibleLogicalRange(r));
          })
          .catch(e => { document.getElementById('ms-' + ticker).textContent = 'Failed: ' + e; });
      });
    });
    </script>"""

    content = f"""
    <section style="margin-bottom:20px">
      <h2>Daily Marubozu Scanner</h2>
      <p style="font-size:.88rem;color:#888;margin-bottom:16px">
        Finds bullish Marubozu candles — the body fills 75%+ of the total range with
        minimal upper and lower wicks. Shows strong, clean buying pressure across the
        entire session. Scored by how complete the body is, whether wicks are near zero,
        volume confirmation, and how many days the price has held above the Marubozu open.
      </p>
      <div class="btn-row" style="margin-bottom:8px">{run_btn}</div>
      <p class="note">{scan_info}</p>
    </section>

    {'<section><h2>Log</h2><pre>' + get_log().replace("<","&lt;") + '</pre></section>' if running and jname == "Marubozu Scan" else ''}

    <section>
      <style>
        .maru-table {{ width:100%; border-collapse:collapse; font-size:.92rem; }}
        .maru-table th {{ text-align:left; padding:10px 14px; color:#777; font-size:.78rem;
                         border-bottom:1px solid #2a2d3e; font-weight:500;
                         cursor:pointer; user-select:none; }}
        .maru-table th:hover {{ color:#aaa; }}
        .maru-table th.sort-asc::after  {{ content:' ▲'; font-size:.6rem; color:#60a5fa; }}
        .maru-table th.sort-desc::after {{ content:' ▼'; font-size:.6rem; color:#60a5fa; }}
        .maru-table td {{ padding:10px 14px; border-bottom:1px solid #151820; vertical-align:middle; }}
        .maru-table .maru-row:hover td {{ background:#1f2235; cursor:pointer; }}
        .maru-table .maru-row.active td {{ background:#1a2235; }}
        .maru-drop td {{ padding:0 !important; }}
        .maru-filter-btn {{ background:#1a1d2e; border:1px solid #2a2d3e; color:#888;
                            padding:6px 16px; border-radius:6px; cursor:pointer; font-size:.82rem; }}
        .maru-filter-btn.active {{ background:#1e3a5f; border-color:#3b82f6; color:#60a5fa; font-weight:600; }}
      </style>

      <div style="background:#0d0f1a;border:1px solid #1e2235;border-radius:8px;padding:14px 16px;margin-bottom:16px">
        <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:10px">
          <span style="color:#aaa;font-size:.82rem;font-weight:600;letter-spacing:.04em">TRADINGVIEW WATCHLIST</span>
          <button onclick="copyMaruList()" id="mtv-copy-btn"
            style="background:#1e3a5f;border:1px solid #3b82f6;color:#60a5fa;padding:5px 14px;
                   border-radius:5px;cursor:pointer;font-size:.78rem;font-weight:600">
            Copy
          </button>
        </div>
        <textarea id="mtv-list" readonly rows="3"
          style="width:100%;background:#080a10;border:1px solid #1a1d2e;border-radius:5px;
                 color:#c7d2fe;font-size:.8rem;padding:8px 10px;resize:vertical;
                 font-family:monospace;box-sizing:border-box;line-height:1.6"></textarea>
        <p style="color:#444;font-size:.72rem;margin:6px 0 0">
          Paste directly into TradingView → Watchlist → Import. Updates when you switch Today / All.
        </p>
      </div>

      <div style="display:flex;align-items:center;gap:8px;margin-bottom:12px">
        <button class="maru-filter-btn active" id="mf-today" onclick="setMaruFilter('today')">Today</button>
        <button class="maru-filter-btn"        id="mf-all"   onclick="setMaruFilter('all')">All Signals</button>
        <span id="maru-count" style="color:#555;font-size:.78rem;margin-left:4px"></span>
      </div>

      <table class="maru-table">
        <thead><tr>
          <th onclick="sortMaru(this)">Ticker</th>
          <th onclick="sortMaru(this)">Date</th>
          <th onclick="sortMaru(this)" style="text-align:center">Score</th>
          <th onclick="sortMaru(this)">Body %</th>
          <th onclick="sortMaru(this)">Upper Wick</th>
          <th onclick="sortMaru(this)">Lower Wick</th>
          <th onclick="sortMaru(this)">Held</th>
          <th onclick="sortMaru(this)">Vol</th>
          <th onclick="sortMaru(this)">Current</th>
          <th onclick="sortMaru(this)">Gain</th>
        </tr></thead>
        <tbody id="maru-tbody">
          {rows_html if rows_html else '<tr><td colspan="10" style="color:#555;padding:20px">No results yet — run the scan.</td></tr>'}
        </tbody>
      </table>
    </section>
    <script>
    function sortMaru(th) {{
      const tbody = document.getElementById('maru-tbody');
      const idx = th.cellIndex;
      const asc = th.classList.contains('sort-desc');
      th.closest('thead').querySelectorAll('th').forEach(h => h.classList.remove('sort-asc','sort-desc'));
      th.classList.add(asc ? 'sort-asc' : 'sort-desc');
      const rows = Array.from(tbody.querySelectorAll('.maru-row'));
      rows.sort((a, b) => {{
        const av = a.cells[idx].textContent.trim();
        const bv = b.cells[idx].textContent.trim();
        const an = parseFloat(av.replace(/[^0-9.-]/g,'')), bn = parseFloat(bv.replace(/[^0-9.-]/g,''));
        const cmp = isNaN(an) ? av.localeCompare(bv) : an - bn;
        return asc ? cmp : -cmp;
      }});
      rows.forEach(r => tbody.appendChild(r));
    }}

    function getMostRecentMaruDate() {{
      let latest = '';
      document.querySelectorAll('.maru-row').forEach(r => {{
        const d = r.dataset.maruDate || '';
        if (d > latest) latest = d;
      }});
      return latest;
    }}

    function setMaruFilter(mode) {{
      document.getElementById('mf-today').classList.toggle('active', mode === 'today');
      document.getElementById('mf-all').classList.toggle('active',   mode === 'all');
      const latestDate = getMostRecentMaruDate();
      let visible = 0;
      document.querySelectorAll('.maru-row').forEach(r => {{
        const show = (mode === 'all') || (r.dataset.maruDate === latestDate);
        r.style.display = show ? '' : 'none';
        if (show) visible++;
        if (!show) {{
          const drop = document.getElementById('mdrop-' + r.dataset.ticker);
          if (drop) {{ drop.remove(); r.classList.remove('active'); }}
        }}
      }});
      document.getElementById('maru-count').textContent = visible + ' signal' + (visible !== 1 ? 's' : '');
      updateMaruList();
    }}

    function updateMaruList() {{
      const tickers = [];
      document.querySelectorAll('.maru-row').forEach(r => {{
        if (r.style.display !== 'none') tickers.push(r.dataset.ticker);
      }});
      document.getElementById('mtv-list').value = tickers.join(',');
    }}

    function copyMaruList() {{
      const ta = document.getElementById('mtv-list');
      ta.select(); ta.setSelectionRange(0, 99999);
      navigator.clipboard.writeText(ta.value).then(() => {{
        const btn = document.getElementById('mtv-copy-btn');
        btn.textContent = 'Copied!';
        btn.style.background = '#14532d';
        btn.style.borderColor = '#22c55e';
        btn.style.color = '#4ade80';
        setTimeout(() => {{
          btn.textContent = 'Copy';
          btn.style.background = '#1e3a5f';
          btn.style.borderColor = '#3b82f6';
          btn.style.color = '#60a5fa';
        }}, 2000);
      }});
    }}

    setMaruFilter('today');
    </script>
    {chart_js}"""

    return page_wrap('Marubozu Scanner', 'marubozu', content, auto_refresh=(running and jname == 'Marubozu Scan'))


# ─── Range Oscillator (Zeiierman) Breakout Scanner ───────────────────────────

def _run_range_oscillator_scan_job():
    global _job_running, _job_name
    with open(LOG_FILE, 'w') as f:
        f.write(f"=== Range Oscillator Scan ===\nStarted: {datetime.now()}\n\n")
    try:
        run_range_oscillator_scan(log_callback=lambda m: open(LOG_FILE, 'a').write(m))
    except Exception as e:
        with open(LOG_FILE, 'a') as f:
            f.write(f"\nERROR: {e}\n")
    finally:
        with _job_lock:
            _job_running = False
            _job_name    = ''


def start_range_oscillator_scan():
    global _job_running, _job_name
    with _job_lock:
        if _job_running:
            return False
        _job_running = True
        _job_name    = 'Range Oscillator Scan'
    threading.Thread(target=_run_range_oscillator_scan_job, daemon=True).start()
    return True


@app.route('/run-range-oscillator')
def run_range_oscillator():
    if not is_admin():
        return redirect('/admin')
    start_range_oscillator_scan()
    return redirect('/range-oscillator')


@app.route('/range-oscillator')
def range_oscillator_page():
    if not is_admin():
        return redirect('/')

    with _job_lock:
        running = _job_running
        jname   = _job_name

    last = load_last_range_oscillator_results()

    if running and jname == 'Range Oscillator Scan':
        run_btn = '<span class="btn btn-off">⏳ Scanning…</span>'
    elif running:
        run_btn = '<span class="btn btn-off">Another job running</span>'
    else:
        run_btn = '<a href="/run-range-oscillator" class="btn btn-blue">▶ Run Range Oscillator Scan</a>'

    def score_color(s):
        if s >= 6:  return '#22c55e'
        if s >= 3:  return '#f59e0b'
        return '#555'

    rows_html = ''
    if last and last.get('results'):
        for r in last['results']:
            sc  = r['score']
            gc  = '#22c55e' if r['gain_pct'] >= 0 else '#ef4444'
            gs  = '+' if r['gain_pct'] >= 0 else ''
            bullish = r['direction'] == 'bullish'
            dir_col = '#22c55e' if bullish else '#ef4444'
            dir_icon = '▲' if bullish else '▽'
            vol_icon = ' ⚡' if r.get('vol_surge') else ''
            rows_html += f"""
            <tr class="rosc-row" data-ticker="{r['ticker']}" data-rosc-date="{r['signal_date']}">
              <td><strong style="color:#60a5fa;font-size:1rem">{r['ticker']}</strong></td>
              <td style="color:#aaa">{r['signal_date']}</td>
              <td style="color:{dir_col};font-weight:600">{dir_icon} {r['direction']}</td>
              <td style="text-align:center">
                <span style="background:{score_color(sc)};color:#fff;padding:3px 10px;
                             border-radius:12px;font-weight:700;font-size:.85rem">{sc}</span>
              </td>
              <td style="color:#fff;font-weight:600">{r['osc']:+.1f}</td>
              <td style="color:#555">{vol_icon if vol_icon else '—'}</td>
              <td style="color:#aaa">{r['days_held']}d</td>
              <td style="color:#fff;font-weight:600">${r['current_price']:,.4f}</td>
              <td style="color:{gc};font-weight:700">{gs}{r['gain_pct']:.2f}%</td>
            </tr>"""

    scan_info = ''
    if last:
        scan_info = (f"Last scan: {last['scan_date']} &nbsp;·&nbsp; "
                     f"{last['total']} signals from {last['tickers_scanned']} tickers")

    chart_js = """
    <script src="https://unpkg.com/lightweight-charts@4.1.3/dist/lightweight-charts.standalone.production.js"></script>
    <script>
    // LightweightCharts v4 vertical line primitive — paneViews() → renderer() → draw()
    class RoscLineRenderer {
      constructor(time, color, chart) {
        this._time = time; this._color = color; this._chart = chart;
      }
      draw(target) {
        const x = this._chart.timeScale().timeToCoordinate(this._time);
        if (x === null) return;
        target.useBitmapCoordinateSpace(scope => {
          const ctx = scope.context;
          const xb = Math.round(x * scope.horizontalPixelRatio);
          ctx.save();
          ctx.beginPath();
          ctx.moveTo(xb, 0);
          ctx.lineTo(xb, scope.bitmapSize.height);
          ctx.strokeStyle = this._color;
          ctx.lineWidth = Math.round(2 * scope.horizontalPixelRatio);
          ctx.setLineDash([6, 4]);
          ctx.stroke();
          ctx.restore();
        });
      }
    }
    class RoscLinePaneView {
      constructor(time, color, chart) {
        this._renderer = new RoscLineRenderer(time, color, chart);
      }
      renderer() { return this._renderer; }
      zOrder()   { return 'normal'; }
    }
    class RoscLine {
      constructor(time, color = '#f59e0b') {
        this._time = time; this._color = color;
        this._chart = null; this._views = [];
      }
      attached({ chart }) {
        this._chart = chart;
        this._views = [new RoscLinePaneView(this._time, this._color, chart)];
      }
      detached()       { this._views = []; }
      paneViews()      { return this._views; }
      updateAllViews() {}
    }

    document.querySelectorAll('.rosc-row').forEach(row => {
      row.addEventListener('click', () => {
        const ticker   = row.dataset.ticker;
        const roscDate = row.dataset.roscDate;
        const existId  = 'rdrop-' + ticker;
        const exist = document.getElementById(existId);
        if (exist) { exist.remove(); row.classList.remove('active'); return; }
        document.querySelectorAll('.rosc-drop').forEach(d => d.remove());
        document.querySelectorAll('.rosc-row.active').forEach(r => r.classList.remove('active'));
        row.classList.add('active');
        const drop = document.createElement('tr');
        drop.id = existId; drop.className = 'rosc-drop';
        drop.innerHTML = `<td colspan="9" style="background:#080a10;padding:16px 20px">
          <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:10px">
            <span style="color:#fff;font-weight:700;font-size:1rem">${ticker}</span>
            <span style="color:#555;font-size:.75rem" id="rs-${ticker}">Loading...</span>
          </div>
          <div id="rm-${ticker}" style="height:420px;background:#0a0c14;border-radius:6px"></div>
          <div id="rv-${ticker}" style="height:65px;background:#0a0c14;border-radius:6px;margin-top:3px"></div>
        </td>`;
        row.parentNode.insertBefore(drop, row.nextSibling);
        fetch('/api/us-chart/' + ticker)
          .then(r => r.json())
          .then(data => {
            if (data.error) { document.getElementById('rs-' + ticker).textContent = data.error; return; }
            document.getElementById('rs-' + ticker).textContent = data.bars + ' bars · ' + data.date_range;
            const chart = LightweightCharts.createChart(document.getElementById('rm-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: true },
              crosshair: { mode: LightweightCharts.CrosshairMode.Normal },
            });
            const candles = chart.addCandlestickSeries({
              upColor: '#22c55e', downColor: '#ef4444',
              borderUpColor: '#22c55e', borderDownColor: '#ef4444',
              wickUpColor: '#22c55e', wickDownColor: '#ef4444',
            });
            candles.setData(data.ohlcv);
            const roscMs = new Date(roscDate).getTime();
            let snapDate = roscDate;
            let minDiff = Infinity;
            for (const bar of data.ohlcv) {
              const diff = Math.abs(new Date(bar.time).getTime() - roscMs);
              if (diff < minDiff) { minDiff = diff; snapDate = bar.time; }
            }
            candles.attachPrimitive(new RoscLine(snapDate));
            const ema5  = chart.addLineSeries({ color: '#60a5fa', lineWidth: 1, title: 'EMA5' });
            const ema26 = chart.addLineSeries({ color: '#f59e0b', lineWidth: 1, title: 'EMA26' });
            ema5.setData(data.ema5); ema26.setData(data.ema26);
            const barCount = data.ohlcv.length;
            chart.timeScale().setVisibleLogicalRange({ from: Math.max(0, barCount - 120), to: barCount + 5 });
            chart.priceScale('right').applyOptions({ scaleMargins: { top: 0.12, bottom: 0.18 } });
            const vc = LightweightCharts.createChart(document.getElementById('rv-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: false },
            });
            const vs = vc.addHistogramSeries({ priceFormat: { type: 'volume' }, priceScaleId: '' });
            vs.priceScale().applyOptions({ scaleMargins: { top: 0.1, bottom: 0 } });
            vs.setData(data.volume); vc.timeScale().fitContent();
            chart.timeScale().subscribeVisibleLogicalRangeChange(r => vc.timeScale().setVisibleLogicalRange(r));
            vc.timeScale().subscribeVisibleLogicalRangeChange(r => chart.timeScale().setVisibleLogicalRange(r));
          })
          .catch(e => { document.getElementById('rs-' + ticker).textContent = 'Failed: ' + e; });
      });
    });
    </script>"""

    content = f"""
    <section style="margin-bottom:20px">
      <h2>Range Oscillator (Zeiierman) Breakout Scanner</h2>
      <p style="font-size:.88rem;color:#888;margin-bottom:16px">
        Flags the first day a ticker's close breaks outside its own ATR-scaled range
        around a volatility-weighted moving average — the oscillator's own "strong
        bullish/bearish" override level, not just a fuzzy extreme reading. Scans both
        directions. Scored by how far past the breakout level the reading is, volume
        confirmation, and how many days the breakout has continued to hold.
      </p>
      <div class="btn-row" style="margin-bottom:8px">{run_btn}</div>
      <p class="note">{scan_info}</p>
    </section>

    {'<section><h2>Log</h2><pre>' + get_log().replace("<","&lt;") + '</pre></section>' if running and jname == "Range Oscillator Scan" else ''}

    <section>
      <style>
        .rosc-table {{ width:100%; border-collapse:collapse; font-size:.92rem; }}
        .rosc-table th {{ text-align:left; padding:10px 14px; color:#777; font-size:.78rem;
                         border-bottom:1px solid #2a2d3e; font-weight:500;
                         cursor:pointer; user-select:none; }}
        .rosc-table th:hover {{ color:#aaa; }}
        .rosc-table th.sort-asc::after  {{ content:' ▲'; font-size:.6rem; color:#60a5fa; }}
        .rosc-table th.sort-desc::after {{ content:' ▼'; font-size:.6rem; color:#60a5fa; }}
        .rosc-table td {{ padding:10px 14px; border-bottom:1px solid #151820; vertical-align:middle; }}
        .rosc-table .rosc-row:hover td {{ background:#1f2235; cursor:pointer; }}
        .rosc-table .rosc-row.active td {{ background:#1a2235; }}
        .rosc-drop td {{ padding:0 !important; }}
        .rosc-filter-btn {{ background:#1a1d2e; border:1px solid #2a2d3e; color:#888;
                            padding:6px 16px; border-radius:6px; cursor:pointer; font-size:.82rem; }}
        .rosc-filter-btn.active {{ background:#1e3a5f; border-color:#3b82f6; color:#60a5fa; font-weight:600; }}
      </style>

      <div style="display:flex;align-items:center;gap:8px;margin-bottom:12px">
        <button class="rosc-filter-btn active" id="rf-today" onclick="setRoscFilter('today')">Today</button>
        <button class="rosc-filter-btn"        id="rf-all"   onclick="setRoscFilter('all')">All Signals</button>
        <span id="rosc-count" style="color:#555;font-size:.78rem;margin-left:4px"></span>
      </div>

      <table class="rosc-table">
        <thead><tr>
          <th onclick="sortRosc(this)">Ticker</th>
          <th onclick="sortRosc(this)">Date</th>
          <th onclick="sortRosc(this)">Direction</th>
          <th onclick="sortRosc(this)" style="text-align:center">Score</th>
          <th onclick="sortRosc(this)">Osc</th>
          <th onclick="sortRosc(this)">Vol</th>
          <th onclick="sortRosc(this)">Held</th>
          <th onclick="sortRosc(this)">Current</th>
          <th onclick="sortRosc(this)">Gain</th>
        </tr></thead>
        <tbody id="rosc-tbody">
          {rows_html if rows_html else '<tr><td colspan="9" style="color:#555;padding:20px">No results yet — run the scan.</td></tr>'}
        </tbody>
      </table>
    </section>
    <script>
    function sortRosc(th) {{
      const tbody = document.getElementById('rosc-tbody');
      const idx = th.cellIndex;
      const asc = th.classList.contains('sort-desc');
      th.closest('thead').querySelectorAll('th').forEach(h => h.classList.remove('sort-asc','sort-desc'));
      th.classList.add(asc ? 'sort-asc' : 'sort-desc');
      const rows = Array.from(tbody.querySelectorAll('.rosc-row'));
      rows.sort((a, b) => {{
        const av = a.cells[idx].textContent.trim();
        const bv = b.cells[idx].textContent.trim();
        const an = parseFloat(av.replace(/[^0-9.-]/g,'')), bn = parseFloat(bv.replace(/[^0-9.-]/g,''));
        const cmp = isNaN(an) ? av.localeCompare(bv) : an - bn;
        return asc ? cmp : -cmp;
      }});
      rows.forEach(r => tbody.appendChild(r));
    }}

    function getMostRecentRoscDate() {{
      let latest = '';
      document.querySelectorAll('.rosc-row').forEach(r => {{
        const d = r.dataset.roscDate || '';
        if (d > latest) latest = d;
      }});
      return latest;
    }}

    function setRoscFilter(mode) {{
      document.getElementById('rf-today').classList.toggle('active', mode === 'today');
      document.getElementById('rf-all').classList.toggle('active',   mode === 'all');
      const latestDate = getMostRecentRoscDate();
      let visible = 0;
      document.querySelectorAll('.rosc-row').forEach(r => {{
        const show = (mode === 'all') || (r.dataset.roscDate === latestDate);
        r.style.display = show ? '' : 'none';
        if (show) visible++;
        if (!show) {{
          const drop = document.getElementById('rdrop-' + r.dataset.ticker);
          if (drop) {{ drop.remove(); r.classList.remove('active'); }}
        }}
      }});
      document.getElementById('rosc-count').textContent = visible + ' signal' + (visible !== 1 ? 's' : '');
    }}

    setRoscFilter('today');
    </script>
    {chart_js}"""

    return page_wrap('Range Oscillator Scanner', 'range-oscillator', content,
                      auto_refresh=(running and jname == 'Range Oscillator Scan'))


# ─── Weekly Swing Low Scanner (Leviathan Swing Points) ───────────────────────

def _run_swing_scan_job():
    global _job_running, _job_name
    with open(LOG_FILE, 'w') as f:
        f.write(f"=== Swing Scan ===\nStarted: {datetime.now()}\n\n")
    try:
        run_swing_scan(log_callback=lambda m: open(LOG_FILE, 'a').write(m))
    except Exception as e:
        with open(LOG_FILE, 'a') as f:
            f.write(f"\nERROR: {e}\n")
    finally:
        with _job_lock:
            _job_running = False
            _job_name    = ''


def start_swing_scan():
    global _job_running, _job_name
    with _job_lock:
        if _job_running:
            return False
        _job_running = True
        _job_name    = 'Swing Scan'
    threading.Thread(target=_run_swing_scan_job, daemon=True).start()
    return True


@app.route('/run-swing')
def run_swing():
    if not is_admin():
        return redirect('/admin')
    start_swing_scan()
    return redirect('/swing')


@app.route('/swing')
def swing_page():
    if not is_admin():
        return redirect('/')

    with _job_lock:
        running = _job_running
        jname   = _job_name

    last = load_last_swing_results()

    if running and jname == 'Swing Scan':
        run_btn = '<span class="btn btn-off">⏳ Scanning…</span>'
    elif running:
        run_btn = '<span class="btn btn-off">Another job running</span>'
    else:
        run_btn = '<a href="/run-swing" class="btn btn-blue">▶ Run Swing Scan</a>'

    def score_color(s):
        if s >= 5:  return '#22c55e'
        if s >= 3:  return '#f59e0b'
        return '#555'

    rows_html = ''
    if last and last.get('results'):
        for r in last['results']:
            sc  = r['score']
            gc  = '#22c55e' if r['bounce_pct'] >= 0 else '#ef4444'
            gs  = '+' if r['bounce_pct'] >= 0 else ''
            filled_icon = '○ Filled' if r.get('filled') else '● Clean'
            filled_col  = '#555' if r.get('filled') else '#22c55e'
            vol_icon = ' ⚡' if r.get('vol_surge') else ''
            rows_html += f"""
            <tr class="swing-row" data-ticker="{r['ticker']}" data-swing-date="{r['pivot_date']}">
              <td><strong style="color:#60a5fa;font-size:1rem">🟢 {r['ticker']}</strong></td>
              <td style="color:#aaa">{r['pivot_date']}</td>
              <td style="color:#888">{r['confirm_date']}</td>
              <td style="text-align:center">
                <span style="background:{score_color(sc)};color:#fff;padding:3px 10px;
                             border-radius:12px;font-weight:700;font-size:.85rem">{sc}</span>
              </td>
              <td style="color:#fff;font-weight:600">${r['pivot_price']:,.4f}</td>
              <td style="color:{filled_col}">{filled_icon}</td>
              <td style="color:#555">{vol_icon if vol_icon else '—'}</td>
              <td style="color:#fff;font-weight:600">${r['current_price']:,.4f}</td>
              <td style="color:{gc};font-weight:700">{gs}{r['bounce_pct']:.2f}%</td>
            </tr>"""

    scan_info = ''
    if last:
        scan_info = (f"Last scan: {last['scan_date']} &nbsp;·&nbsp; "
                     f"{last['total']} signals from {last['tickers_scanned']} tickers")

    chart_js = """
    <script src="https://unpkg.com/lightweight-charts@4.1.3/dist/lightweight-charts.standalone.production.js"></script>
    <script>
    // LightweightCharts v4 vertical line primitive — paneViews() → renderer() → draw()
    class SwingLineRenderer {
      constructor(time, color, chart) {
        this._time = time; this._color = color; this._chart = chart;
      }
      draw(target) {
        const x = this._chart.timeScale().timeToCoordinate(this._time);
        if (x === null) return;
        target.useBitmapCoordinateSpace(scope => {
          const ctx = scope.context;
          const xb = Math.round(x * scope.horizontalPixelRatio);
          ctx.save();
          ctx.beginPath();
          ctx.moveTo(xb, 0);
          ctx.lineTo(xb, scope.bitmapSize.height);
          ctx.strokeStyle = this._color;
          ctx.lineWidth = Math.round(2 * scope.horizontalPixelRatio);
          ctx.setLineDash([6, 4]);
          ctx.stroke();
          ctx.restore();
        });
      }
    }
    class SwingLinePaneView {
      constructor(time, color, chart) {
        this._renderer = new SwingLineRenderer(time, color, chart);
      }
      renderer() { return this._renderer; }
      zOrder()   { return 'normal'; }
    }
    class SwingLine {
      constructor(time, color = '#22c55e') {
        this._time = time; this._color = color;
        this._chart = null; this._views = [];
      }
      attached({ chart }) {
        this._chart = chart;
        this._views = [new SwingLinePaneView(this._time, this._color, chart)];
      }
      detached()       { this._views = []; }
      paneViews()      { return this._views; }
      updateAllViews() {}
    }

    document.querySelectorAll('.swing-row').forEach(row => {
      row.addEventListener('click', () => {
        const ticker    = row.dataset.ticker;
        const swingDate = row.dataset.swingDate;
        const existId   = 'sdrop-' + ticker;
        const exist = document.getElementById(existId);
        if (exist) { exist.remove(); row.classList.remove('active'); return; }
        document.querySelectorAll('.swing-drop').forEach(d => d.remove());
        document.querySelectorAll('.swing-row.active').forEach(r => r.classList.remove('active'));
        row.classList.add('active');
        const drop = document.createElement('tr');
        drop.id = existId; drop.className = 'swing-drop';
        drop.innerHTML = `<td colspan="9" style="background:#080a10;padding:16px 20px">
          <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:10px">
            <span style="color:#fff;font-weight:700;font-size:1rem">${ticker}</span>
            <span style="color:#555;font-size:.75rem" id="ss-${ticker}">Loading...</span>
          </div>
          <div id="sm-${ticker}" style="height:420px;background:#0a0c14;border-radius:6px"></div>
          <div id="sv-${ticker}" style="height:65px;background:#0a0c14;border-radius:6px;margin-top:3px"></div>
        </td>`;
        row.parentNode.insertBefore(drop, row.nextSibling);
        fetch('/api/us-chart/' + ticker)
          .then(r => r.json())
          .then(data => {
            if (data.error) { document.getElementById('ss-' + ticker).textContent = data.error; return; }
            document.getElementById('ss-' + ticker).textContent = data.bars + ' bars · ' + data.date_range;
            const chart = LightweightCharts.createChart(document.getElementById('sm-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: true },
              crosshair: { mode: LightweightCharts.CrosshairMode.Normal },
            });
            const candles = chart.addCandlestickSeries({
              upColor: '#22c55e', downColor: '#ef4444',
              borderUpColor: '#22c55e', borderDownColor: '#ef4444',
              wickUpColor: '#22c55e', wickDownColor: '#ef4444',
            });
            candles.setData(data.ohlcv);
            const swingMs = new Date(swingDate).getTime();
            let snapDate = swingDate;
            let minDiff = Infinity;
            for (const bar of data.ohlcv) {
              const diff = Math.abs(new Date(bar.time).getTime() - swingMs);
              if (diff < minDiff) { minDiff = diff; snapDate = bar.time; }
            }
            candles.attachPrimitive(new SwingLine(snapDate));
            const ema5  = chart.addLineSeries({ color: '#60a5fa', lineWidth: 1, title: 'EMA5' });
            const ema26 = chart.addLineSeries({ color: '#f59e0b', lineWidth: 1, title: 'EMA26' });
            ema5.setData(data.ema5); ema26.setData(data.ema26);
            const barCount = data.ohlcv.length;
            chart.timeScale().setVisibleLogicalRange({ from: Math.max(0, barCount - 140), to: barCount + 5 });
            chart.priceScale('right').applyOptions({ scaleMargins: { top: 0.12, bottom: 0.18 } });
            const vc = LightweightCharts.createChart(document.getElementById('sv-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: false },
            });
            const vs = vc.addHistogramSeries({ priceFormat: { type: 'volume' }, priceScaleId: '' });
            vs.priceScale().applyOptions({ scaleMargins: { top: 0.1, bottom: 0 } });
            vs.setData(data.volume); vc.timeScale().fitContent();
            chart.timeScale().subscribeVisibleLogicalRangeChange(r => vc.timeScale().setVisibleLogicalRange(r));
            vc.timeScale().subscribeVisibleLogicalRangeChange(r => chart.timeScale().setVisibleLogicalRange(r));
          })
          .catch(e => { document.getElementById('ss-' + ticker).textContent = 'Failed: ' + e; });
      });
    });
    </script>"""

    content = f"""
    <section style="margin-bottom:20px">
      <h2>Weekly Swing Low Scanner — Leviathan Swing Points</h2>
      <p style="font-size:.88rem;color:#888;margin-bottom:16px">
        Finds "green dot" swing lows confirming THIS WEEK on the weekly chart — a
        low from 10 weeks ago that's held as the lowest low through the 10 weeks
        since, translated from the "Swing Points and Liquidity" indicator (crypto
        Open Interest overlay dropped — not applicable to equities). Scored by how
        far price has bounced since the low, whether the liquidity level is still
        unfilled (price hasn't traded back through it), and volume confirmation.
      </p>
      <div class="btn-row" style="margin-bottom:8px">{run_btn}</div>
      <p class="note">{scan_info}</p>
    </section>

    {'<section><h2>Log</h2><pre>' + get_log().replace("<","&lt;") + '</pre></section>' if running and jname == "Swing Scan" else ''}

    <section>
      <style>
        .swing-table {{ width:100%; border-collapse:collapse; font-size:.92rem; }}
        .swing-table th {{ text-align:left; padding:10px 14px; color:#777; font-size:.78rem;
                          border-bottom:1px solid #2a2d3e; font-weight:500;
                          cursor:pointer; user-select:none; }}
        .swing-table th:hover {{ color:#aaa; }}
        .swing-table th.sort-asc::after  {{ content:' ▲'; font-size:.6rem; color:#60a5fa; }}
        .swing-table th.sort-desc::after {{ content:' ▼'; font-size:.6rem; color:#60a5fa; }}
        .swing-table td {{ padding:10px 14px; border-bottom:1px solid #151820; vertical-align:middle; }}
        .swing-table .swing-row:hover td {{ background:#1f2235; cursor:pointer; }}
        .swing-table .swing-row.active td {{ background:#1a2235; }}
        .swing-drop td {{ padding:0 !important; }}
      </style>

      <table class="swing-table">
        <thead><tr>
          <th onclick="sortSwing(this)">Ticker</th>
          <th onclick="sortSwing(this)">Pivot Week</th>
          <th onclick="sortSwing(this)">Confirmed</th>
          <th onclick="sortSwing(this)" style="text-align:center">Score</th>
          <th onclick="sortSwing(this)">Low</th>
          <th onclick="sortSwing(this)">Zone</th>
          <th onclick="sortSwing(this)">Vol</th>
          <th onclick="sortSwing(this)">Current</th>
          <th onclick="sortSwing(this)">Bounce</th>
        </tr></thead>
        <tbody id="swing-tbody">
          {rows_html if rows_html else '<tr><td colspan="9" style="color:#555;padding:20px">No results yet — run the scan.</td></tr>'}
        </tbody>
      </table>
    </section>
    <script>
    function sortSwing(th) {{
      const tbody = document.getElementById('swing-tbody');
      const idx = th.cellIndex;
      const asc = th.classList.contains('sort-desc');
      th.closest('thead').querySelectorAll('th').forEach(h => h.classList.remove('sort-asc','sort-desc'));
      th.classList.add(asc ? 'sort-asc' : 'sort-desc');
      const rows = Array.from(tbody.querySelectorAll('.swing-row'));
      rows.sort((a, b) => {{
        const av = a.cells[idx].textContent.trim();
        const bv = b.cells[idx].textContent.trim();
        const an = parseFloat(av.replace(/[^0-9.-]/g,'')), bn = parseFloat(bv.replace(/[^0-9.-]/g,''));
        const cmp = isNaN(an) ? av.localeCompare(bv) : an - bn;
        return asc ? cmp : -cmp;
      }});
      rows.forEach(r => tbody.appendChild(r));
    }}
    </script>
    {chart_js}"""

    return page_wrap('Swing Low Scanner', 'swing', content, auto_refresh=(running and jname == 'Swing Scan'))


# ─── Weekly Higher-Low Scanner (Leviathan Swing Points, 3-dot shape) ─────────

def _run_higher_low_scan_job():
    global _job_running, _job_name
    with open(LOG_FILE, 'w') as f:
        f.write(f"=== Higher Low Scan ===\nStarted: {datetime.now()}\n\n")
    try:
        run_higher_low_scan(log_callback=lambda m: open(LOG_FILE, 'a').write(m))
    except Exception as e:
        with open(LOG_FILE, 'a') as f:
            f.write(f"\nERROR: {e}\n")
    finally:
        with _job_lock:
            _job_running = False
            _job_name    = ''


def start_higher_low_scan():
    global _job_running, _job_name
    with _job_lock:
        if _job_running:
            return False
        _job_running = True
        _job_name    = 'Higher Low Scan'
    threading.Thread(target=_run_higher_low_scan_job, daemon=True).start()
    return True


@app.route('/run-higher-low')
def run_higher_low():
    if not is_admin():
        return redirect('/admin')
    start_higher_low_scan()
    return redirect('/higher-low')


@app.route('/higher-low')
def higher_low_page():
    if not is_admin():
        return redirect('/')

    with _job_lock:
        running = _job_running
        jname   = _job_name

    last = load_last_higher_low_results()

    if running and jname == 'Higher Low Scan':
        run_btn = '<span class="btn btn-off">⏳ Scanning…</span>'
    elif running:
        run_btn = '<span class="btn btn-off">Another job running</span>'
    else:
        run_btn = '<a href="/run-higher-low" class="btn btn-blue">▶ Run Higher Low Scan</a>'

    def score_color(s):
        if s >= 6:  return '#22c55e'
        if s >= 3:  return '#f59e0b'
        return '#555'

    rows_html = ''
    if last and last.get('results'):
        for r in last['results']:
            sc = r['score']
            reclaim_icon = '✓ Reclaimed A' if r.get('reclaimed_a') else '— below A'
            reclaim_col  = '#22c55e' if r.get('reclaimed_a') else '#888'
            vol_icon = ' ⚡' if r.get('vol_surge') else ''
            rows_html += f"""
            <tr class="hl-row" data-ticker="{r['ticker']}" data-b-date="{r['b_date']}" data-c-date="{r['c_date']}">
              <td><strong style="color:#60a5fa;font-size:1rem">🟢 {r['ticker']}</strong></td>
              <td style="color:#aaa">{r['a_date']} @ ${r['a_price']:,.2f}</td>
              <td style="color:#ef4444">{r['b_date']} @ ${r['b_price']:,.2f} (-{r['flush_pct']:.1f}%)</td>
              <td style="color:#22c55e">{r['c_date']} @ ${r['c_price']:,.2f} (+{r['recover_pct']:.1f}%)</td>
              <td style="text-align:center">
                <span style="background:{score_color(sc)};color:#fff;padding:3px 10px;
                             border-radius:12px;font-weight:700;font-size:.85rem">{sc}</span>
              </td>
              <td style="color:{reclaim_col}">{reclaim_icon}</td>
              <td style="color:#555">{vol_icon if vol_icon else '—'}</td>
              <td style="color:#fff;font-weight:600">${r['current_price']:,.4f}</td>
            </tr>"""

    scan_info = ''
    if last:
        scan_info = (f"Last scan: {last['scan_date']} &nbsp;·&nbsp; "
                     f"{last['total']} signals from {last['tickers_scanned']} tickers")

    chart_js = """
    <script src="https://unpkg.com/lightweight-charts@4.1.3/dist/lightweight-charts.standalone.production.js"></script>
    <script>
    // LightweightCharts v4 vertical line primitive — paneViews() → renderer() → draw()
    class HLLineRenderer {
      constructor(time, color, chart) {
        this._time = time; this._color = color; this._chart = chart;
      }
      draw(target) {
        const x = this._chart.timeScale().timeToCoordinate(this._time);
        if (x === null) return;
        target.useBitmapCoordinateSpace(scope => {
          const ctx = scope.context;
          const xb = Math.round(x * scope.horizontalPixelRatio);
          ctx.save();
          ctx.beginPath();
          ctx.moveTo(xb, 0);
          ctx.lineTo(xb, scope.bitmapSize.height);
          ctx.strokeStyle = this._color;
          ctx.lineWidth = Math.round(2 * scope.horizontalPixelRatio);
          ctx.setLineDash([6, 4]);
          ctx.stroke();
          ctx.restore();
        });
      }
    }
    class HLLinePaneView {
      constructor(time, color, chart) {
        this._renderer = new HLLineRenderer(time, color, chart);
      }
      renderer() { return this._renderer; }
      zOrder()   { return 'normal'; }
    }
    class HLLine {
      constructor(time, color) {
        this._time = time; this._color = color;
        this._chart = null; this._views = [];
      }
      attached({ chart }) {
        this._chart = chart;
        this._views = [new HLLinePaneView(this._time, this._color, chart)];
      }
      detached()       { this._views = []; }
      paneViews()      { return this._views; }
      updateAllViews() {}
    }

    document.querySelectorAll('.hl-row').forEach(row => {
      row.addEventListener('click', () => {
        const ticker = row.dataset.ticker;
        const bDate  = row.dataset.bDate;
        const cDate  = row.dataset.cDate;
        const existId = 'hldrop-' + ticker;
        const exist = document.getElementById(existId);
        if (exist) { exist.remove(); row.classList.remove('active'); return; }
        document.querySelectorAll('.hl-drop').forEach(d => d.remove());
        document.querySelectorAll('.hl-row.active').forEach(r => r.classList.remove('active'));
        row.classList.add('active');
        const drop = document.createElement('tr');
        drop.id = existId; drop.className = 'hl-drop';
        drop.innerHTML = `<td colspan="8" style="background:#080a10;padding:16px 20px">
          <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:10px">
            <span style="color:#fff;font-weight:700;font-size:1rem">${ticker}</span>
            <span style="color:#555;font-size:.75rem" id="hls-${ticker}">Loading...</span>
          </div>
          <div id="hlm-${ticker}" style="height:420px;background:#0a0c14;border-radius:6px"></div>
          <div id="hlv-${ticker}" style="height:65px;background:#0a0c14;border-radius:6px;margin-top:3px"></div>
        </td>`;
        row.parentNode.insertBefore(drop, row.nextSibling);
        fetch('/api/us-chart/' + ticker)
          .then(r => r.json())
          .then(data => {
            if (data.error) { document.getElementById('hls-' + ticker).textContent = data.error; return; }
            document.getElementById('hls-' + ticker).textContent = data.bars + ' bars · ' + data.date_range;
            const chart = LightweightCharts.createChart(document.getElementById('hlm-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: true },
              crosshair: { mode: LightweightCharts.CrosshairMode.Normal },
            });
            const candles = chart.addCandlestickSeries({
              upColor: '#22c55e', downColor: '#ef4444',
              borderUpColor: '#22c55e', borderDownColor: '#ef4444',
              wickUpColor: '#22c55e', wickDownColor: '#ef4444',
            });
            candles.setData(data.ohlcv);
            function snapTo(dateStr) {
              const ms = new Date(dateStr).getTime();
              let snap = dateStr, minDiff = Infinity;
              for (const bar of data.ohlcv) {
                const diff = Math.abs(new Date(bar.time).getTime() - ms);
                if (diff < minDiff) { minDiff = diff; snap = bar.time; }
              }
              return snap;
            }
            candles.attachPrimitive(new HLLine(snapTo(bDate), '#ef4444'));
            candles.attachPrimitive(new HLLine(snapTo(cDate), '#22c55e'));
            const ema5  = chart.addLineSeries({ color: '#60a5fa', lineWidth: 1, title: 'EMA5' });
            const ema26 = chart.addLineSeries({ color: '#f59e0b', lineWidth: 1, title: 'EMA26' });
            ema5.setData(data.ema5); ema26.setData(data.ema26);
            const barCount = data.ohlcv.length;
            chart.timeScale().setVisibleLogicalRange({ from: Math.max(0, barCount - 180), to: barCount + 5 });
            chart.priceScale('right').applyOptions({ scaleMargins: { top: 0.12, bottom: 0.18 } });
            const vc = LightweightCharts.createChart(document.getElementById('hlv-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: false },
            });
            const vs = vc.addHistogramSeries({ priceFormat: { type: 'volume' }, priceScaleId: '' });
            vs.priceScale().applyOptions({ scaleMargins: { top: 0.1, bottom: 0 } });
            vs.setData(data.volume); vc.timeScale().fitContent();
            chart.timeScale().subscribeVisibleLogicalRangeChange(r => vc.timeScale().setVisibleLogicalRange(r));
            vc.timeScale().subscribeVisibleLogicalRangeChange(r => chart.timeScale().setVisibleLogicalRange(r));
          })
          .catch(e => { document.getElementById('hls-' + ticker).textContent = 'Failed: ' + e; });
      });
    });
    </script>"""

    content = f"""
    <section style="margin-bottom:20px">
      <h2>Weekly Higher-Low Scanner — Leviathan Swing Points</h2>
      <p style="font-size:.88rem;color:#888;margin-bottom:16px">
        Finds the 3-dot "higher low" shape on the weekly chart: a swing low (A),
        then an obvious flush below it (B, at least 3% deeper), then a later
        swing low confirming back above the flush (C) — one final shakeout
        before the uptrend structure resumes. Red marker = the flush (B),
        green marker = the confirming higher low (C). Only shows patterns
        where C confirmed within the last 12 weeks.
      </p>
      <div class="btn-row" style="margin-bottom:8px">{run_btn}</div>
      <p class="note">{scan_info}</p>
    </section>

    {'<section><h2>Log</h2><pre>' + get_log().replace("<","&lt;") + '</pre></section>' if running and jname == "Higher Low Scan" else ''}

    <section>
      <style>
        .hl-table {{ width:100%; border-collapse:collapse; font-size:.88rem; }}
        .hl-table th {{ text-align:left; padding:10px 14px; color:#777; font-size:.78rem;
                       border-bottom:1px solid #2a2d3e; font-weight:500; }}
        .hl-table td {{ padding:10px 14px; border-bottom:1px solid #151820; vertical-align:middle; }}
        .hl-table .hl-row:hover td {{ background:#1f2235; cursor:pointer; }}
        .hl-table .hl-row.active td {{ background:#1a2235; }}
        .hl-drop td {{ padding:0 !important; }}
      </style>

      <table class="hl-table">
        <thead><tr>
          <th>Ticker</th>
          <th>A (prior low)</th>
          <th>B (flush)</th>
          <th>C (higher low)</th>
          <th style="text-align:center">Score</th>
          <th>Structure</th>
          <th>Vol</th>
          <th>Current</th>
        </tr></thead>
        <tbody id="hl-tbody">
          {rows_html if rows_html else '<tr><td colspan="8" style="color:#555;padding:20px">No results yet — run the scan.</td></tr>'}
        </tbody>
      </table>
    </section>
    {chart_js}"""

    return page_wrap('Higher Low Scanner', 'higher-low', content,
                      auto_refresh=(running and jname == 'Higher Low Scan'))


# ─── Gap Down Double Bottom Scanner ───────────────────────────────────────────

def _run_doublebottom_scan_job():
    global _job_running, _job_name
    with open(LOG_FILE, 'w') as f:
        f.write(f"=== Gap Down Double Bottom Scan ===\nStarted: {datetime.now()}\n\n")
    try:
        run_doublebottom_scan(log_callback=lambda m: open(LOG_FILE, 'a').write(m))
    except Exception as e:
        with open(LOG_FILE, 'a') as f:
            f.write(f"\nERROR: {e}\n")
    finally:
        with _job_lock:
            _job_running = False
            _job_name    = ''


def start_doublebottom_scan():
    global _job_running, _job_name
    with _job_lock:
        if _job_running:
            return False
        _job_running = True
        _job_name    = 'Gap Down Double Bottom Scan'
    threading.Thread(target=_run_doublebottom_scan_job, daemon=True).start()
    return True


@app.route('/run-doublebottom')
def run_doublebottom():
    if not is_admin():
        return redirect('/admin')
    start_doublebottom_scan()
    return redirect('/doublebottom')


@app.route('/doublebottom')
def doublebottom_page():
    if not is_admin():
        return redirect('/')

    with _job_lock:
        running = _job_running
        jname   = _job_name

    last = load_last_doublebottom_results()

    # Guard against stale results saved by the old (pre-gap-down) schema —
    # rendering would otherwise KeyError on the new field names. Drop any
    # rows that don't look like the current schema instead of crashing.
    if last and last.get('results'):
        fresh_results = [r for r in last['results'] if 'gap_date' in r]
        if len(fresh_results) != len(last['results']):
            last = dict(last, results=fresh_results, total=len(fresh_results))

    if running and jname == 'Gap Down Double Bottom Scan':
        run_btn = '<span class="btn btn-off">⏳ Scanning…</span>'
    elif running:
        run_btn = '<span class="btn btn-off">Another job running</span>'
    else:
        run_btn = '<a href="/run-doublebottom" class="btn btn-blue">▶ Run Gap Down Double Bottom Scan</a>'

    def score_color(s):
        if s >= 55: return '#22c55e'
        if s >= 40: return '#f59e0b'
        return '#555'

    def tier_color(label):
        return {'10%+': '#b91c1c', '7.5%+': '#ef4444', '5%+': '#f59e0b', '2.5%+': '#60a5fa'}.get(label, '#555')

    rows_html = ''
    if last and last.get('results'):
        for r in last['results']:
            sc = r['score']
            touches = r['touches']
            touch_badge = f"{touches}× bottom" if touches == 2 else f"{touches}× bottoms 🔥"
            vol_icon = ' ⚡' if r.get('vol_surge') else ''
            recov_icon = ' ↩' if r.get('recovered_intraday') else ''
            bottoms_json = json.dumps([b['date'] for b in r['bottoms']])
            rows_html += f"""
            <tr class="db-row" data-ticker="{r['ticker']}" data-bottoms='{bottoms_json}'
                data-neckline-date="{r['neckline_date']}" data-gap-pct="{r['gap_pct']}">
              <td><strong style="color:#60a5fa;font-size:1rem">🟢 {r['ticker']}</strong></td>
              <td style="color:#ef4444">
                {r['gap_date']}
                <span style="background:{tier_color(r['gap_tier'])};color:#fff;padding:1px 7px;
                             border-radius:10px;font-size:.72rem;font-weight:700;margin-left:4px">{r['gap_pct']:.1f}%</span>
              </td>
              <td style="color:#aaa">${r['gap_low']:,.2f}</td>
              <td style="color:#22c55e">{r['first_bottom_date']} @ ${r['first_bottom_price']:,.2f}</td>
              <td style="color:#f59e0b">${r['neckline']:,.2f} (+{r['neckline_pct']:.0f}%)</td>
              <td style="color:#aaa">{touch_badge}</td>
              <td style="text-align:center">
                <span style="background:{score_color(sc)};color:#fff;padding:3px 10px;
                             border-radius:12px;font-weight:700;font-size:.85rem">{sc}</span>
              </td>
              <td style="color:#555">{vol_icon}{recov_icon if vol_icon or recov_icon else '—'}</td>
              <td style="color:#fff;font-weight:600">${r['price']:,.4f}</td>
              <td style="color:#888">1:{r['rr']}</td>
            </tr>"""

    scan_info = ''
    if last:
        scan_info = (f"Last scan: {last['scan_date']} &nbsp;·&nbsp; "
                     f"{last['total']} signals from {last['tickers_scanned']} tickers")

    chart_js = """
    <script src="https://unpkg.com/lightweight-charts@4.1.3/dist/lightweight-charts.standalone.production.js"></script>
    <script>
    // LightweightCharts v4 vertical line primitive — paneViews() → renderer() → draw()
    class DBLineRenderer {
      constructor(time, color, chart) {
        this._time = time; this._color = color; this._chart = chart;
      }
      draw(target) {
        const x = this._chart.timeScale().timeToCoordinate(this._time);
        if (x === null) return;
        target.useBitmapCoordinateSpace(scope => {
          const ctx = scope.context;
          const xb = Math.round(x * scope.horizontalPixelRatio);
          ctx.save();
          ctx.beginPath();
          ctx.moveTo(xb, 0);
          ctx.lineTo(xb, scope.bitmapSize.height);
          ctx.strokeStyle = this._color;
          ctx.lineWidth = Math.round(2 * scope.horizontalPixelRatio);
          ctx.setLineDash([6, 4]);
          ctx.stroke();
          ctx.restore();
        });
      }
    }
    class DBLinePaneView {
      constructor(time, color, chart) {
        this._renderer = new DBLineRenderer(time, color, chart);
      }
      renderer() { return this._renderer; }
      zOrder()   { return 'normal'; }
    }
    class DBLine {
      constructor(time, color) {
        this._time = time; this._color = color;
        this._chart = null; this._views = [];
      }
      attached({ chart }) {
        this._chart = chart;
        this._views = [new DBLinePaneView(this._time, this._color, chart)];
      }
      detached()       { this._views = []; }
      paneViews()      { return this._views; }
      updateAllViews() {}
    }

    document.querySelectorAll('.db-row').forEach(row => {
      row.addEventListener('click', () => {
        const ticker      = row.dataset.ticker;
        const bottomDates = JSON.parse(row.dataset.bottoms);
        const necklineDate = row.dataset.necklineDate;
        const existId = 'dbdrop-' + ticker;
        const exist = document.getElementById(existId);
        if (exist) { exist.remove(); row.classList.remove('active'); return; }
        document.querySelectorAll('.db-drop').forEach(d => d.remove());
        document.querySelectorAll('.db-row.active').forEach(r => r.classList.remove('active'));
        row.classList.add('active');
        const drop = document.createElement('tr');
        drop.id = existId; drop.className = 'db-drop';
        drop.innerHTML = `<td colspan="10" style="background:#080a10;padding:16px 20px">
          <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:10px">
            <span style="color:#fff;font-weight:700;font-size:1rem">${ticker}</span>
            <span style="color:#555;font-size:.75rem" id="dbs-${ticker}">Loading...</span>
          </div>
          <div id="dbm-${ticker}" style="height:420px;background:#0a0c14;border-radius:6px"></div>
          <div id="dbv-${ticker}" style="height:65px;background:#0a0c14;border-radius:6px;margin-top:3px"></div>
        </td>`;
        row.parentNode.insertBefore(drop, row.nextSibling);
        fetch('/api/us-chart/' + ticker)
          .then(r => r.json())
          .then(data => {
            if (data.error) { document.getElementById('dbs-' + ticker).textContent = data.error; return; }
            document.getElementById('dbs-' + ticker).textContent = data.bars + ' bars · ' + data.date_range;
            const chart = LightweightCharts.createChart(document.getElementById('dbm-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: true },
              crosshair: { mode: LightweightCharts.CrosshairMode.Normal },
            });
            const candles = chart.addCandlestickSeries({
              upColor: '#22c55e', downColor: '#ef4444',
              borderUpColor: '#22c55e', borderDownColor: '#ef4444',
              wickUpColor: '#22c55e', wickDownColor: '#ef4444',
            });
            candles.setData(data.ohlcv);
            function snapTo(dateStr) {
              const ms = new Date(dateStr).getTime();
              let snap = dateStr, minDiff = Infinity;
              for (const bar of data.ohlcv) {
                const diff = Math.abs(new Date(bar.time).getTime() - ms);
                if (diff < minDiff) { minDiff = diff; snap = bar.time; }
              }
              return snap;
            }
            // Green dashed line at every confirmed bottom touch, amber at the neckline peak
            bottomDates.forEach(d => candles.attachPrimitive(new DBLine(snapTo(d), '#22c55e')));
            candles.attachPrimitive(new DBLine(snapTo(necklineDate), '#f59e0b'));
            const ema5  = chart.addLineSeries({ color: '#60a5fa', lineWidth: 1, title: 'EMA5' });
            const ema26 = chart.addLineSeries({ color: '#f59e0b', lineWidth: 1, title: 'EMA26' });
            ema5.setData(data.ema5); ema26.setData(data.ema26);
            const barCount = data.ohlcv.length;
            chart.timeScale().setVisibleLogicalRange({ from: Math.max(0, barCount - 180), to: barCount + 5 });
            chart.priceScale('right').applyOptions({ scaleMargins: { top: 0.12, bottom: 0.18 } });
            const vc = LightweightCharts.createChart(document.getElementById('dbv-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: false },
            });
            const vs = vc.addHistogramSeries({ priceFormat: { type: 'volume' }, priceScaleId: '' });
            vs.priceScale().applyOptions({ scaleMargins: { top: 0.1, bottom: 0 } });
            vs.setData(data.volume); vc.timeScale().fitContent();
            chart.timeScale().subscribeVisibleLogicalRangeChange(r => vc.timeScale().setVisibleLogicalRange(r));
            vc.timeScale().subscribeVisibleLogicalRangeChange(r => chart.timeScale().setVisibleLogicalRange(r));
          })
          .catch(e => { document.getElementById('dbs-' + ticker).textContent = 'Failed: ' + e; });
      });
    });
    </script>"""

    content = f"""
    <section style="margin-bottom:20px">
      <h2>Gap Down Double Bottom Scanner</h2>
      <p style="font-size:.88rem;color:#888;margin-bottom:16px">
        Finds stocks that gapped down in the last day/week to a price that
        matches an earlier confirmed double-bottom support — the gap landed
        almost exactly on a level the stock already proved as support once
        before. Price must also sit in the 0-25% zone of its dollar-range
        bucket, and the neckline between the two lows must clear 8%+. Green
        markers = confirmed bottom touches (prior support + the gap low),
        amber marker = the neckline peak. Use the tier buttons to filter by
        gap size.
      </p>
      <div class="btn-row" style="margin-bottom:8px">{run_btn}</div>
      <p class="note">{scan_info}</p>
    </section>

    {'<section><h2>Log</h2><pre>' + get_log().replace("<","&lt;") + '</pre></section>' if running and jname == "Gap Down Double Bottom Scan" else ''}

    <section>
      <style>
        .db-table {{ width:100%; border-collapse:collapse; font-size:.88rem; }}
        .db-table th {{ text-align:left; padding:10px 14px; color:#777; font-size:.78rem;
                       border-bottom:1px solid #2a2d3e; font-weight:500; }}
        .db-table td {{ padding:10px 14px; border-bottom:1px solid #151820; vertical-align:middle; }}
        .db-table .db-row:hover td {{ background:#1f2235; cursor:pointer; }}
        .db-table .db-row.active td {{ background:#1a2235; }}
        .db-drop td {{ padding:0 !important; }}
        .db-filter-btn {{ background:#1a1d2e; border:1px solid #2a2d3e; color:#888;
                          padding:6px 16px; border-radius:6px; cursor:pointer; font-size:.82rem; }}
        .db-filter-btn.active {{ background:#1e3a5f; border-color:#3b82f6; color:#60a5fa; font-weight:600; }}
      </style>

      <div style="display:flex;align-items:center;gap:8px;margin-bottom:12px">
        <span style="color:#666;font-size:.78rem;margin-right:2px">Gap size:</span>
        <button class="db-filter-btn active" id="db-t25" onclick="setGapFilter(2.5)">2.5%+</button>
        <button class="db-filter-btn"        id="db-t50" onclick="setGapFilter(5)">5%+</button>
        <button class="db-filter-btn"        id="db-t75" onclick="setGapFilter(7.5)">7.5%+</button>
        <button class="db-filter-btn"        id="db-t100" onclick="setGapFilter(10)">10%+</button>
        <span id="db-count" style="color:#555;font-size:.78rem;margin-left:4px"></span>
      </div>

      <table class="db-table">
        <thead><tr>
          <th>Ticker</th>
          <th>Gap</th>
          <th>Gap Low</th>
          <th>Prior Bottom</th>
          <th>Neckline</th>
          <th>Touches</th>
          <th style="text-align:center">Score</th>
          <th>Vol/Recov</th>
          <th>Current</th>
          <th>R:R</th>
        </tr></thead>
        <tbody id="db-tbody">
          {rows_html if rows_html else '<tr><td colspan="10" style="color:#555;padding:20px">No results yet — run the scan.</td></tr>'}
        </tbody>
      </table>
    </section>
    <script>
    const DB_TIER_IDS = {{ 2.5: 'db-t25', 5: 'db-t50', 7.5: 'db-t75', 10: 'db-t100' }};
    function setGapFilter(tier) {{
      document.querySelectorAll('.db-filter-btn').forEach(b => b.classList.remove('active'));
      document.getElementById(DB_TIER_IDS[tier]).classList.add('active');
      let visible = 0;
      document.querySelectorAll('.db-row').forEach(r => {{
        const gapPct = parseFloat(r.dataset.gapPct);
        const show = gapPct <= -tier;
        r.style.display = show ? '' : 'none';
        if (show) visible++;
        if (!show) {{
          const drop = document.getElementById('dbdrop-' + r.dataset.ticker);
          if (drop) {{ drop.remove(); r.classList.remove('active'); }}
        }}
      }});
      document.getElementById('db-count').textContent = visible + ' signal' + (visible !== 1 ? 's' : '');
    }}
    setGapFilter(2.5);
    </script>
    {chart_js}"""

    return page_wrap('Gap Down Double Bottom Scanner', 'doublebottom', content,
                      auto_refresh=(running and jname == 'Gap Down Double Bottom Scan'))


# ─── Recession / Inflation Watchlist ──────────────────────────────────────────

def _run_recession_scan_job():
    global _job_running, _job_name
    with open(LOG_FILE, 'w') as f:
        f.write(f"=== Recession Watchlist Scan ===\nStarted: {datetime.now()}\n\n")
    try:
        run_recession_scan(log_callback=lambda m: open(LOG_FILE, 'a').write(m))
    except Exception as e:
        with open(LOG_FILE, 'a') as f:
            f.write(f"\nERROR: {e}\n")
    finally:
        with _job_lock:
            _job_running = False
            _job_name    = ''


def start_recession_scan():
    global _job_running, _job_name
    with _job_lock:
        if _job_running:
            return False
        _job_running = True
        _job_name    = 'Recession Watchlist Scan'
    threading.Thread(target=_run_recession_scan_job, daemon=True).start()
    return True


@app.route('/run-recession')
def run_recession():
    if not is_admin():
        return redirect('/admin')
    start_recession_scan()
    return redirect('/recession')


@app.route('/recession')
def recession_page():
    if not is_admin():
        return redirect('/')

    with _job_lock:
        running = _job_running
        jname   = _job_name

    last = load_last_recession_results()
    by_ticker = {r['ticker']: r for r in last['results']} if last else {}

    if running and jname == 'Recession Watchlist Scan':
        run_btn = '<span class="btn btn-off">⏳ Scanning…</span>'
    elif running:
        run_btn = '<span class="btn btn-off">Another job running</span>'
    else:
        run_btn = '<a href="/run-recession" class="btn btn-blue">▶ Check Watchlist vs Blue Lines</a>'

    status_colors = {
        'AT BLUE': '#2563eb', 'APPROACHING': '#0891b2', 'ON BLUE': '#475569',
        'DIVING': '#b91c1c', 'WATCH': '#333',
    }

    def row_html(ticker, note):
        tv = RECESSION_TV_SYMBOL(ticker)
        link = (f'<a href="https://www.tradingview.com/chart/?symbol={tv}" target="_blank" '
                f'style="color:#60a5fa;font-weight:700">{ticker}</a>')
        r = by_ticker.get(ticker)
        if not r:
            return f"""<tr><td>{link}</td><td style="color:#888">{note}</td>
              <td colspan="7" style="color:#555">not scanned yet</td></tr>"""
        st = r['status']
        blue = f"${r['blue_low']:,.2f}–${r['blue_high']:,.2f}" if r['blue_low'] is not None else '—'
        dist = f"{r['blue_dist']:+.1f}%" if r['blue_dist'] is not None else '—'
        run  = f"{r['run_ranges']:.1f}" + (' ⚠' if r['extended'] else '')
        return f"""<tr>
          <td>{link}</td>
          <td style="color:#888;font-size:.82rem">{note}</td>
          <td><span style="background:{status_colors[st]};color:#fff;padding:2px 9px;
                     border-radius:10px;font-size:.72rem;font-weight:700">{st}</span></td>
          <td style="color:#fff;font-weight:600">${r['price']:,.2f}</td>
          <td style="color:{'#ef4444' if r['drawdown'] <= -15 else '#aaa'}">{r['drawdown']:+.1f}%</td>
          <td style="color:#aaa">${r['ath']:,.2f} <span style="color:#555">{r['ath_date']}</span></td>
          <td style="color:#60a5fa">{blue}</td>
          <td style="color:#aaa">{dist}</td>
          <td style="color:#aaa">{run}</td>
          <td style="color:#aaa">{r['blue_holds']}</td>
        </tr>"""

    head = """<tr><th>Ticker</th><th>Why</th><th>Status</th><th>Price</th><th>From ATH</th>
      <th>ATH</th><th>Blue line</th><th>To blue</th><th>Run (ranges)</th><th>Blue holds</th></tr>"""

    # Shortlist: every thesis stock that has dived and is at / approaching a blue line
    notes = {t: n for th in RECESSION_THEMES for t, n in th['tickers'].items()}
    hot = [r for r in (last['results'] if last else [])
           if r.get('core') and r['status'] in ('AT BLUE', 'APPROACHING')]
    if hot:
        hot_rows = ''.join(row_html(r['ticker'], notes.get(r['ticker'], '')) for r in hot)
        shortlist = f"""
        <section style="margin-bottom:28px">
          <h2 style="color:#60a5fa">Nose-dived onto the blue line</h2>
          <p style="color:#888;font-size:.85rem;margin-top:-6px">Vice / get-to-work stocks {abs(RECESSION_NOSE_DIVE):.0f}%+
             off their all-time high, sitting in or within {RECESSION_APPROACH:.0f}% of a blue band.</p>
          <div style="overflow-x:auto"><table class="data-table">{head}{hot_rows}</table></div>
        </section>"""
    elif last:
        shortlist = '<p style="color:#888">No vice / get-to-work stock is at or approaching a blue line right now.</p>'
    else:
        shortlist = ''

    theme_html = ''
    for pillar, pillar_title in RECESSION_PILLARS:
        pillar_color = '#888' if pillar == 'side' else '#e5e7eb'
        theme_html += (f'<h2 style="margin:34px 0 14px;color:{pillar_color};border-bottom:1px solid #2a2d3e;'
                       f'padding-bottom:6px">{pillar_title}</h2>')
        if pillar == 'side':
            theme_html += ('<p style="color:#777;font-size:.85rem;margin-top:-6px">Not vices or work '
                           'enablers — tracked for context only, never in the shortlist or TradingView list.</p>')
        for th in RECESSION_THEMES:
            if th['pillar'] != pillar:
                continue
            added = (' <span style="color:#f59e0b;font-size:.72rem;font-weight:600">SUGGESTED ADDITION</span>'
                     if th.get('added') else '')
            rows = ''.join(row_html(t, n) for t, n in th['tickers'].items())
            theme_html += f"""
            <section style="margin-bottom:24px">
              <h3 style="margin-bottom:4px">{th['title']}{added}</h3>
              <p style="color:#999;font-size:.85rem;margin:0 0 8px;font-style:italic">{th['rationale']}</p>
              <div style="overflow-x:auto"><table class="data-table">{head}{rows}</table></div>
            </section>"""

    scan_info = ''
    if last:
        scan_info = (f"Last check: {last['scan_date']} &nbsp;·&nbsp; {last['total']} at/approaching "
                     f"a blue line from {last['tickers_scanned']} tickers")
        if last.get('failed'):
            scan_info += f" &nbsp;·&nbsp; <span style='color:#ef4444'>no data: {', '.join(last['failed'])}</span>"

    content = f"""
    <style>
    .data-table {{ width:100%; border-collapse:collapse; font-size:.85rem; }}
    .data-table th {{ text-align:left; padding:8px 10px; color:#555; border-bottom:1px solid #2a2d3e;
                      font-weight:500; white-space:nowrap; }}
    .data-table td {{ padding:8px 10px; border-bottom:1px solid #151820; }}
    .data-table tr:hover td {{ background:#1f2235; }}
    </style>
    <h1>Recession / Inflation Watchlist</h1>
    <p style="color:#e5e7eb;max-width:780px;font-size:1.05rem"><b>Cut away the economic bullshit:</b> the only
      things that gain value are <b>vices</b> and products that let the working class <b>get to work and work
      longer hours</b>.</p>
    <p style="color:#aaa;max-width:780px">People don't riot when they realise they're trapped — they adapt
      and work more. Smokes, booze, a punt, energy drinks, coffee, stimulants, fast food to work, fuel, and a
      cheap car kept on the road. Long-term plan: wait for these to nose-dive onto a blue line the way MCD
      does, instead of monitoring trades live.</p>
    <p style="color:#666;font-size:.8rem;max-width:780px">Blue band = 20–30% of each big range
      (big range = $100 for a $100–999 stock, $10 for $10–99, $1 under $10) — e.g. MCD $120–130, $220–230.
      Monthly bars, full history. <b>Run (ranges)</b> = how many big ranges the move into the ATH covered
      (⚠ = 2.5+, "never 3"). <b>Blue holds</b> = months whose low tagged a blue band and closed back above it.</p>
    <div class="btn-row" style="margin:14px 0">{run_btn}</div>
    <p style="color:#888;font-size:.82rem">{scan_info}</p>
    {shortlist}
    {theme_html}
    <section style="margin-top:28px">
      <h3>TradingView watchlist <span style="color:#777;font-size:.8rem;font-weight:400">(vices + get to work only)</span></h3>
      <textarea id="rec-tv" readonly style="width:100%;height:70px;background:#111;color:#ccc;
                border:1px solid #333;border-radius:6px;padding:8px;font-size:.8rem">{RECESSION_TV_LIST()}</textarea>
      <button id="rec-copy" class="btn btn-blue" style="margin-top:6px"
        onclick="navigator.clipboard.writeText(document.getElementById('rec-tv').value)
                 .then(()=>{{this.textContent='Copied!'}})">Copy</button>
    </section>"""

    return page_wrap('Recession Watchlist', 'recession', content,
                      auto_refresh=(running and jname == 'Recession Watchlist Scan'))


# ─── Weekly Extreme-Exit Scanner (Range Oscillator cooling off) ─────────────

def _run_extreme_exit_scan_job():
    global _job_running, _job_name
    with open(LOG_FILE, 'w') as f:
        f.write(f"=== Extreme Exit Scan ===\nStarted: {datetime.now()}\n\n")
    try:
        run_extreme_exit_scan(log_callback=lambda m: open(LOG_FILE, 'a').write(m))
    except Exception as e:
        with open(LOG_FILE, 'a') as f:
            f.write(f"\nERROR: {e}\n")
    finally:
        with _job_lock:
            _job_running = False
            _job_name    = ''


def start_extreme_exit_scan():
    global _job_running, _job_name
    with _job_lock:
        if _job_running:
            return False
        _job_running = True
        _job_name    = 'Extreme Exit Scan'
    threading.Thread(target=_run_extreme_exit_scan_job, daemon=True).start()
    return True


@app.route('/run-extreme-exit')
def run_extreme_exit():
    if not is_admin():
        return redirect('/admin')
    start_extreme_exit_scan()
    return redirect('/extreme-exit')


@app.route('/extreme-exit')
def extreme_exit_page():
    if not is_admin():
        return redirect('/')

    with _job_lock:
        running = _job_running
        jname   = _job_name

    last = load_last_extreme_exit_results()

    if running and jname == 'Extreme Exit Scan':
        run_btn = '<span class="btn btn-off">⏳ Scanning…</span>'
    elif running:
        run_btn = '<span class="btn btn-off">Another job running</span>'
    else:
        run_btn = '<a href="/run-extreme-exit" class="btn btn-blue">▶ Run Extreme Exit Scan</a>'

    def score_color(s):
        if s >= 5:  return '#22c55e'
        if s >= 3:  return '#f59e0b'
        return '#555'

    rows_html = ''
    if last and last.get('results'):
        for r in last['results']:
            sc = r['score']
            gc = '#22c55e' if r['gain_pct'] >= 0 else '#ef4444'
            gs = '+' if r['gain_pct'] >= 0 else ''
            sustained_icon = '⏳ Sustained' if r.get('sustained') else '—'
            osc_now = f"{r['osc_now']:+.1f}" if r.get('osc_now') is not None else '—'
            rows_html += f"""
            <tr class="ee-row" data-ticker="{r['ticker']}" data-extreme-date="{r['extreme_date']}" data-exit-date="{r['exit_date']}">
              <td><strong style="color:#60a5fa;font-size:1rem">🟢 {r['ticker']}</strong></td>
              <td style="color:#ef4444">{r['extreme_date']} (osc {r['osc_at_extreme']:+.1f})</td>
              <td style="color:#22c55e">{r['exit_date']} (osc {osc_now})</td>
              <td style="text-align:center">
                <span style="background:{score_color(sc)};color:#fff;padding:3px 10px;
                             border-radius:12px;font-weight:700;font-size:.85rem">{sc}</span>
              </td>
              <td style="color:#888">{sustained_icon}</td>
              <td style="color:#fff;font-weight:600">${r['current_price']:,.4f}</td>
              <td style="color:{gc};font-weight:700">{gs}{r['gain_pct']:.2f}%</td>
            </tr>"""

    scan_info = ''
    if last:
        scan_info = (f"Last scan: {last['scan_date']} &nbsp;·&nbsp; "
                     f"{last['total']} signals from {last['tickers_scanned']} tickers")

    chart_js = """
    <script src="https://unpkg.com/lightweight-charts@4.1.3/dist/lightweight-charts.standalone.production.js"></script>
    <script>
    // LightweightCharts v4 vertical line primitive — paneViews() → renderer() → draw()
    class EELineRenderer {
      constructor(time, color, chart) {
        this._time = time; this._color = color; this._chart = chart;
      }
      draw(target) {
        const x = this._chart.timeScale().timeToCoordinate(this._time);
        if (x === null) return;
        target.useBitmapCoordinateSpace(scope => {
          const ctx = scope.context;
          const xb = Math.round(x * scope.horizontalPixelRatio);
          ctx.save();
          ctx.beginPath();
          ctx.moveTo(xb, 0);
          ctx.lineTo(xb, scope.bitmapSize.height);
          ctx.strokeStyle = this._color;
          ctx.lineWidth = Math.round(2 * scope.horizontalPixelRatio);
          ctx.setLineDash([6, 4]);
          ctx.stroke();
          ctx.restore();
        });
      }
    }
    class EELinePaneView {
      constructor(time, color, chart) {
        this._renderer = new EELineRenderer(time, color, chart);
      }
      renderer() { return this._renderer; }
      zOrder()   { return 'normal'; }
    }
    class EELine {
      constructor(time, color) {
        this._time = time; this._color = color;
        this._chart = null; this._views = [];
      }
      attached({ chart }) {
        this._chart = chart;
        this._views = [new EELinePaneView(this._time, this._color, chart)];
      }
      detached()       { this._views = []; }
      paneViews()      { return this._views; }
      updateAllViews() {}
    }

    document.querySelectorAll('.ee-row').forEach(row => {
      row.addEventListener('click', () => {
        const ticker      = row.dataset.ticker;
        const extremeDate = row.dataset.extremeDate;
        const exitDate    = row.dataset.exitDate;
        const existId = 'eedrop-' + ticker;
        const exist = document.getElementById(existId);
        if (exist) { exist.remove(); row.classList.remove('active'); return; }
        document.querySelectorAll('.ee-drop').forEach(d => d.remove());
        document.querySelectorAll('.ee-row.active').forEach(r => r.classList.remove('active'));
        row.classList.add('active');
        const drop = document.createElement('tr');
        drop.id = existId; drop.className = 'ee-drop';
        drop.innerHTML = `<td colspan="7" style="background:#080a10;padding:16px 20px">
          <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:10px">
            <span style="color:#fff;font-weight:700;font-size:1rem">${ticker}</span>
            <span style="color:#555;font-size:.75rem" id="ees-${ticker}">Loading...</span>
          </div>
          <div id="eem-${ticker}" style="height:420px;background:#0a0c14;border-radius:6px"></div>
          <div id="eev-${ticker}" style="height:65px;background:#0a0c14;border-radius:6px;margin-top:3px"></div>
        </td>`;
        row.parentNode.insertBefore(drop, row.nextSibling);
        fetch('/api/us-chart/' + ticker)
          .then(r => r.json())
          .then(data => {
            if (data.error) { document.getElementById('ees-' + ticker).textContent = data.error; return; }
            document.getElementById('ees-' + ticker).textContent = data.bars + ' bars · ' + data.date_range;
            const chart = LightweightCharts.createChart(document.getElementById('eem-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: true },
              crosshair: { mode: LightweightCharts.CrosshairMode.Normal },
            });
            const candles = chart.addCandlestickSeries({
              upColor: '#22c55e', downColor: '#ef4444',
              borderUpColor: '#22c55e', borderDownColor: '#ef4444',
              wickUpColor: '#22c55e', wickDownColor: '#ef4444',
            });
            candles.setData(data.ohlcv);
            function snapTo(dateStr) {
              const ms = new Date(dateStr).getTime();
              let snap = dateStr, minDiff = Infinity;
              for (const bar of data.ohlcv) {
                const diff = Math.abs(new Date(bar.time).getTime() - ms);
                if (diff < minDiff) { minDiff = diff; snap = bar.time; }
              }
              return snap;
            }
            candles.attachPrimitive(new EELine(snapTo(extremeDate), '#ef4444'));
            candles.attachPrimitive(new EELine(snapTo(exitDate), '#22c55e'));
            const ema5  = chart.addLineSeries({ color: '#60a5fa', lineWidth: 1, title: 'EMA5' });
            const ema26 = chart.addLineSeries({ color: '#f59e0b', lineWidth: 1, title: 'EMA26' });
            ema5.setData(data.ema5); ema26.setData(data.ema26);
            const barCount = data.ohlcv.length;
            chart.timeScale().setVisibleLogicalRange({ from: Math.max(0, barCount - 180), to: barCount + 5 });
            chart.priceScale('right').applyOptions({ scaleMargins: { top: 0.12, bottom: 0.18 } });
            const vc = LightweightCharts.createChart(document.getElementById('eev-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: false },
            });
            const vs = vc.addHistogramSeries({ priceFormat: { type: 'volume' }, priceScaleId: '' });
            vs.priceScale().applyOptions({ scaleMargins: { top: 0.1, bottom: 0 } });
            vs.setData(data.volume); vc.timeScale().fitContent();
            chart.timeScale().subscribeVisibleLogicalRangeChange(r => vc.timeScale().setVisibleLogicalRange(r));
            vc.timeScale().subscribeVisibleLogicalRangeChange(r => chart.timeScale().setVisibleLogicalRange(r));
          })
          .catch(e => { document.getElementById('ees-' + ticker).textContent = 'Failed: ' + e; });
      });
    });
    </script>"""

    content = f"""
    <section style="margin-bottom:20px">
      <h2>Weekly Extreme-Exit Scanner — Range Oscillator Cooling Off</h2>
      <p style="font-size:.88rem;color:#888;margin-bottom:16px">
        The mirror of the Range Oscillator scanner: instead of a fresh weekly
        breakdown starting, this finds tickers where a weekly strong-bearish
        extreme just STOPPED confirming — last week closed outside the normal
        volatility range, this week didn't. Red marker = the extreme week,
        green marker = the exit week. Scored by how deep the extreme was,
        whether the oscillator is actively climbing back (not just barely
        exiting), and whether the extreme was sustained 2+ weeks.
      </p>
      <div class="btn-row" style="margin-bottom:8px">{run_btn}</div>
      <p class="note">{scan_info}</p>
    </section>

    {'<section><h2>Log</h2><pre>' + get_log().replace("<","&lt;") + '</pre></section>' if running and jname == "Extreme Exit Scan" else ''}

    <section>
      <style>
        .ee-table {{ width:100%; border-collapse:collapse; font-size:.88rem; }}
        .ee-table th {{ text-align:left; padding:10px 14px; color:#777; font-size:.78rem;
                       border-bottom:1px solid #2a2d3e; font-weight:500; }}
        .ee-table td {{ padding:10px 14px; border-bottom:1px solid #151820; vertical-align:middle; }}
        .ee-table .ee-row:hover td {{ background:#1f2235; cursor:pointer; }}
        .ee-table .ee-row.active td {{ background:#1a2235; }}
        .ee-drop td {{ padding:0 !important; }}
      </style>

      <table class="ee-table">
        <thead><tr>
          <th>Ticker</th>
          <th>Extreme Week</th>
          <th>Exit Week</th>
          <th style="text-align:center">Score</th>
          <th>Duration</th>
          <th>Current</th>
          <th>Since Low</th>
        </tr></thead>
        <tbody id="ee-tbody">
          {rows_html if rows_html else '<tr><td colspan="7" style="color:#555;padding:20px">No results yet — run the scan.</td></tr>'}
        </tbody>
      </table>
    </section>
    {chart_js}"""

    return page_wrap('Extreme Exit Scanner', 'extreme-exit', content,
                      auto_refresh=(running and jname == 'Extreme Exit Scan'))


# ─── Extreme Scanner (TD Buy/Sell + ADX Momentum Warning) ────────────────────

def _run_extreme_scan_job():
    global _job_running, _job_name
    with open(LOG_FILE, 'w') as f:
        f.write(f"=== Extreme Scan ===\nStarted: {datetime.now()}\n\n")
    try:
        run_extreme_scan(log_callback=lambda m: open(LOG_FILE, 'a').write(m))
    except Exception as e:
        with open(LOG_FILE, 'a') as f:
            f.write(f"\nERROR: {e}\n")
    finally:
        with _job_lock:
            _job_running = False
            _job_name    = ''


def start_extreme_scan():
    global _job_running, _job_name
    with _job_lock:
        if _job_running:
            return False
        _job_running = True
        _job_name    = 'Extreme Scan'
    threading.Thread(target=_run_extreme_scan_job, daemon=True).start()
    return True


@app.route('/run-extreme')
def run_extreme():
    if not is_admin():
        return redirect('/admin')
    start_extreme_scan()
    return redirect('/extreme')


@app.route('/extreme')
def extreme_page():
    if not is_admin():
        return redirect('/')

    with _job_lock:
        running = _job_running
        jname   = _job_name

    last = load_last_extreme_results()

    if running and jname == 'Extreme Scan':
        run_btn = '<span class="btn btn-off">⏳ Scanning…</span>'
    elif running:
        run_btn = '<span class="btn btn-off">Another job running</span>'
    else:
        run_btn = '<a href="/run-extreme" class="btn btn-blue">▶ Run Extreme Scan</a>'

    def score_color(s):
        if s >= 7:  return '#22c55e'
        if s >= 4:  return '#f59e0b'
        return '#555'

    dir_color = {'bullish': '#22c55e', 'bearish': '#ef4444', 'mixed': '#a78bfa'}
    dir_icon  = {'bullish': '▲', 'bearish': '▽', 'mixed': '◆'}

    rows_html = ''
    if last and last.get('results'):
        for r in last['results']:
            sc  = r['score']
            gc  = '#22c55e' if r['gain_pct'] >= 0 else '#ef4444'
            gs  = '+' if r['gain_pct'] >= 0 else ''
            dcl = dir_color.get(r['direction'], '#888')
            dic = dir_icon.get(r['direction'], '')
            sig_badges = ' '.join(
                f'<span style="background:#1a1d2e;border:1px solid #2a2d3e;color:#ccc;'
                f'padding:2px 8px;border-radius:10px;font-size:.72rem;margin-right:3px;'
                f'white-space:nowrap">{s}</span>'
                for s in r['signals']
            )
            adx_sig_txt = f"{r['adx_signal']:+.1f}" if r['adx_signal'] is not None else '—'
            rows_html += f"""
            <tr class="extreme-row" data-ticker="{r['ticker']}" data-signal-date="{r['signal_date']}">
              <td><strong style="color:#60a5fa;font-size:1rem">{r['ticker']}</strong></td>
              <td style="color:#aaa">{r['signal_date']}</td>
              <td style="text-align:center">
                <span style="background:{score_color(sc)};color:#fff;padding:3px 10px;
                             border-radius:12px;font-weight:700;font-size:.85rem">{sc}</span>
              </td>
              <td>{sig_badges}</td>
              <td style="color:{dcl};font-weight:600">{dic} {r['direction']}</td>
              <td style="color:#fff;font-weight:600">{r['td_buy_count']}</td>
              <td style="color:#fff;font-weight:600">{r['td_sell_count']}</td>
              <td style="color:#888">{adx_sig_txt}</td>
              <td style="color:#fff;font-weight:600">${r['current_price']:,.4f}</td>
              <td style="color:{gc};font-weight:700">{gs}{r['gain_pct']:.2f}%</td>
            </tr>"""

    scan_info = ''
    if last:
        scan_info = (f"Last scan: {last['scan_date']} &nbsp;·&nbsp; "
                     f"{last['total']} signals from {last['tickers_scanned']} tickers")

    chart_js = """
    <script src="https://unpkg.com/lightweight-charts@4.1.3/dist/lightweight-charts.standalone.production.js"></script>
    <script>
    // LightweightCharts v4 vertical line primitive — paneViews() → renderer() → draw()
    class ExtremeLineRenderer {
      constructor(time, color, chart) {
        this._time = time; this._color = color; this._chart = chart;
      }
      draw(target) {
        const x = this._chart.timeScale().timeToCoordinate(this._time);
        if (x === null) return;
        target.useBitmapCoordinateSpace(scope => {
          const ctx = scope.context;
          const xb = Math.round(x * scope.horizontalPixelRatio);
          ctx.save();
          ctx.beginPath();
          ctx.moveTo(xb, 0);
          ctx.lineTo(xb, scope.bitmapSize.height);
          ctx.strokeStyle = this._color;
          ctx.lineWidth = Math.round(2 * scope.horizontalPixelRatio);
          ctx.setLineDash([6, 4]);
          ctx.stroke();
          ctx.restore();
        });
      }
    }
    class ExtremeLinePaneView {
      constructor(time, color, chart) {
        this._renderer = new ExtremeLineRenderer(time, color, chart);
      }
      renderer() { return this._renderer; }
      zOrder()   { return 'normal'; }
    }
    class ExtremeLine {
      constructor(time, color = '#a78bfa') {
        this._time = time; this._color = color;
        this._chart = null; this._views = [];
      }
      attached({ chart }) {
        this._chart = chart;
        this._views = [new ExtremeLinePaneView(this._time, this._color, chart)];
      }
      detached()       { this._views = []; }
      paneViews()      { return this._views; }
      updateAllViews() {}
    }

    document.querySelectorAll('.extreme-row').forEach(row => {
      row.addEventListener('click', () => {
        const ticker     = row.dataset.ticker;
        const signalDate = row.dataset.signalDate;
        const existId    = 'edrop-' + ticker;
        const exist = document.getElementById(existId);
        if (exist) { exist.remove(); row.classList.remove('active'); return; }
        document.querySelectorAll('.extreme-drop').forEach(d => d.remove());
        document.querySelectorAll('.extreme-row.active').forEach(r => r.classList.remove('active'));
        row.classList.add('active');
        const drop = document.createElement('tr');
        drop.id = existId; drop.className = 'extreme-drop';
        drop.innerHTML = `<td colspan="10" style="background:#080a10;padding:16px 20px">
          <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:10px">
            <span style="color:#fff;font-weight:700;font-size:1rem">${ticker}</span>
            <span style="color:#555;font-size:.75rem" id="es-${ticker}">Loading...</span>
          </div>
          <div id="em-${ticker}" style="height:420px;background:#0a0c14;border-radius:6px"></div>
          <div id="ev-${ticker}" style="height:65px;background:#0a0c14;border-radius:6px;margin-top:3px"></div>
        </td>`;
        row.parentNode.insertBefore(drop, row.nextSibling);
        fetch('/api/us-chart/' + ticker)
          .then(r => r.json())
          .then(data => {
            if (data.error) { document.getElementById('es-' + ticker).textContent = data.error; return; }
            document.getElementById('es-' + ticker).textContent = data.bars + ' bars · ' + data.date_range;
            const chart = LightweightCharts.createChart(document.getElementById('em-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: true },
              crosshair: { mode: LightweightCharts.CrosshairMode.Normal },
            });
            const candles = chart.addCandlestickSeries({
              upColor: '#22c55e', downColor: '#ef4444',
              borderUpColor: '#22c55e', borderDownColor: '#ef4444',
              wickUpColor: '#22c55e', wickDownColor: '#ef4444',
            });
            candles.setData(data.ohlcv);
            // Snap the marker to the closest bar to the signal date
            const sigMs = new Date(signalDate).getTime();
            let snapDate = signalDate;
            let minDiff = Infinity;
            for (const bar of data.ohlcv) {
              const diff = Math.abs(new Date(bar.time).getTime() - sigMs);
              if (diff < minDiff) { minDiff = diff; snapDate = bar.time; }
            }
            candles.attachPrimitive(new ExtremeLine(snapDate));
            const ema5  = chart.addLineSeries({ color: '#60a5fa', lineWidth: 1, title: 'EMA5' });
            const ema26 = chart.addLineSeries({ color: '#f59e0b', lineWidth: 1, title: 'EMA26' });
            ema5.setData(data.ema5); ema26.setData(data.ema26);
            const barCount = data.ohlcv.length;
            chart.timeScale().setVisibleLogicalRange({ from: Math.max(0, barCount - 120), to: barCount + 5 });
            chart.priceScale('right').applyOptions({ scaleMargins: { top: 0.12, bottom: 0.18 } });
            const vc = LightweightCharts.createChart(document.getElementById('ev-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: false },
            });
            const vs = vc.addHistogramSeries({ priceFormat: { type: 'volume' }, priceScaleId: '' });
            vs.priceScale().applyOptions({ scaleMargins: { top: 0.1, bottom: 0 } });
            vs.setData(data.volume); vc.timeScale().fitContent();
            chart.timeScale().subscribeVisibleLogicalRangeChange(r => vc.timeScale().setVisibleLogicalRange(r));
            vc.timeScale().subscribeVisibleLogicalRangeChange(r => chart.timeScale().setVisibleLogicalRange(r));
          })
          .catch(e => { document.getElementById('es-' + ticker).textContent = 'Failed: ' + e; });
      });
    });
    </script>"""

    content = f"""
    <section style="margin-bottom:20px">
      <h2>Daily Extreme Scanner</h2>
      <p style="font-size:.88rem;color:#888;margin-bottom:16px">
        Combines two exhaustion/momentum signals — a TD Sequential-style setup counter
        (fires at 8 and 9 consecutive closes below/above the close 4 bars back) and an
        ADX Momentum Change Warning (flags an established trend's momentum rolling over).
        Either one triggers a row; both are always shown together for context, with a
        bonus score when they agree on direction the same day.
      </p>
      <div class="btn-row" style="margin-bottom:8px">{run_btn}</div>
      <p class="note">{scan_info}</p>
    </section>

    {'<section><h2>Log</h2><pre>' + get_log().replace("<","&lt;") + '</pre></section>' if running and jname == "Extreme Scan" else ''}

    <section>
      <style>
        .extreme-table {{ width:100%; border-collapse:collapse; font-size:.92rem; }}
        .extreme-table th {{ text-align:left; padding:10px 14px; color:#777; font-size:.78rem;
                             border-bottom:1px solid #2a2d3e; font-weight:500;
                             cursor:pointer; user-select:none; }}
        .extreme-table th:hover {{ color:#aaa; }}
        .extreme-table th.sort-asc::after  {{ content:' ▲'; font-size:.6rem; color:#60a5fa; }}
        .extreme-table th.sort-desc::after {{ content:' ▼'; font-size:.6rem; color:#60a5fa; }}
        .extreme-table td {{ padding:10px 14px; border-bottom:1px solid #151820; vertical-align:middle; }}
        .extreme-table .extreme-row:hover td {{ background:#1f2235; cursor:pointer; }}
        .extreme-table .extreme-row.active td {{ background:#1a2235; }}
        .extreme-drop td {{ padding:0 !important; }}
        .extreme-filter-btn {{ background:#1a1d2e; border:1px solid #2a2d3e; color:#888;
                               padding:6px 16px; border-radius:6px; cursor:pointer; font-size:.82rem; }}
        .extreme-filter-btn.active {{ background:#1e3a5f; border-color:#3b82f6; color:#60a5fa; font-weight:600; }}
      </style>

      <div style="background:#0d0f1a;border:1px solid #1e2235;border-radius:8px;padding:14px 16px;margin-bottom:16px">
        <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:10px">
          <span style="color:#aaa;font-size:.82rem;font-weight:600;letter-spacing:.04em">TRADINGVIEW WATCHLIST</span>
          <button onclick="copyExtremeList()" id="etv-copy-btn"
            style="background:#1e3a5f;border:1px solid #3b82f6;color:#60a5fa;padding:5px 14px;
                   border-radius:5px;cursor:pointer;font-size:.78rem;font-weight:600">
            Copy
          </button>
        </div>
        <textarea id="etv-list" readonly rows="3"
          style="width:100%;background:#080a10;border:1px solid #1a1d2e;border-radius:5px;
                 color:#c7d2fe;font-size:.8rem;padding:8px 10px;resize:vertical;
                 font-family:monospace;box-sizing:border-box;line-height:1.6"></textarea>
        <p style="color:#444;font-size:.72rem;margin:6px 0 0">
          Paste directly into TradingView → Watchlist → Import. Updates when you switch Today / All.
        </p>
      </div>

      <div style="display:flex;align-items:center;gap:8px;margin-bottom:12px">
        <button class="extreme-filter-btn active" id="ef-today" onclick="setExtremeFilter('today')">Today</button>
        <button class="extreme-filter-btn"         id="ef-all"   onclick="setExtremeFilter('all')">All Signals</button>
        <span id="extreme-count" style="color:#555;font-size:.78rem;margin-left:4px"></span>
      </div>
      <table class="extreme-table">
        <thead><tr>
          <th onclick="sortExtreme(this)">Ticker</th>
          <th onclick="sortExtreme(this)">Date</th>
          <th onclick="sortExtreme(this)" style="text-align:center">Score</th>
          <th>Signals</th>
          <th onclick="sortExtreme(this)">Direction</th>
          <th onclick="sortExtreme(this)">TD Buy</th>
          <th onclick="sortExtreme(this)">TD Sell</th>
          <th onclick="sortExtreme(this)">ADX Sig</th>
          <th onclick="sortExtreme(this)">Current</th>
          <th onclick="sortExtreme(this)">Gain</th>
        </tr></thead>
        <tbody id="extreme-tbody">
          {rows_html if rows_html else '<tr><td colspan="10" style="color:#555;padding:20px">No results yet — run the scan.</td></tr>'}
        </tbody>
      </table>
    </section>
    <script>
    function sortExtreme(th) {{
      const tbody = document.getElementById('extreme-tbody');
      const idx = th.cellIndex;
      const asc = th.classList.contains('sort-desc');
      th.closest('thead').querySelectorAll('th').forEach(h => h.classList.remove('sort-asc','sort-desc'));
      th.classList.add(asc ? 'sort-asc' : 'sort-desc');
      const rows = Array.from(tbody.querySelectorAll('.extreme-row'));
      rows.sort((a, b) => {{
        const av = a.cells[idx].textContent.trim();
        const bv = b.cells[idx].textContent.trim();
        const an = parseFloat(av.replace(/[^0-9.-]/g,'')), bn = parseFloat(bv.replace(/[^0-9.-]/g,''));
        const cmp = isNaN(an) ? av.localeCompare(bv) : an - bn;
        return asc ? cmp : -cmp;
      }});
      rows.forEach(r => tbody.appendChild(r));
    }}

    function getMostRecentExtremeDate() {{
      let latest = '';
      document.querySelectorAll('.extreme-row').forEach(r => {{
        const d = r.dataset.signalDate || '';
        if (d > latest) latest = d;
      }});
      return latest;
    }}

    function setExtremeFilter(mode) {{
      document.getElementById('ef-today').classList.toggle('active', mode === 'today');
      document.getElementById('ef-all').classList.toggle('active',   mode === 'all');
      const latestDate = getMostRecentExtremeDate();
      let visible = 0;
      document.querySelectorAll('.extreme-row').forEach(r => {{
        const show = (mode === 'all') || (r.dataset.signalDate === latestDate);
        r.style.display = show ? '' : 'none';
        if (show) visible++;
        if (!show) {{
          const drop = document.getElementById('edrop-' + r.dataset.ticker);
          if (drop) {{ drop.remove(); r.classList.remove('active'); }}
        }}
      }});
      document.getElementById('extreme-count').textContent = visible + ' signal' + (visible !== 1 ? 's' : '');
      updateExtremeList();
    }}

    function updateExtremeList() {{
      const tickers = [];
      document.querySelectorAll('.extreme-row').forEach(r => {{
        if (r.style.display !== 'none') tickers.push(r.dataset.ticker);
      }});
      document.getElementById('etv-list').value = tickers.join(',');
    }}

    function copyExtremeList() {{
      const ta = document.getElementById('etv-list');
      ta.select();
      ta.setSelectionRange(0, 99999);
      navigator.clipboard.writeText(ta.value).then(() => {{
        const btn = document.getElementById('etv-copy-btn');
        btn.textContent = 'Copied!';
        btn.style.background = '#14532d';
        btn.style.borderColor = '#22c55e';
        btn.style.color = '#4ade80';
        setTimeout(() => {{
          btn.textContent = 'Copy';
          btn.style.background = '#1e3a5f';
          btn.style.borderColor = '#3b82f6';
          btn.style.color = '#60a5fa';
        }}, 2000);
      }});
    }}

    setExtremeFilter('today');
    </script>
    {chart_js}"""

    return page_wrap('Extreme Scanner', 'extreme', content, auto_refresh=(running and jname == 'Extreme Scan'))


# ─── Price Channel Scanner ────────────────────────────────────────────────────

def _run_price_channel_scan_job():
    global _job_running, _job_name
    with open(LOG_FILE, 'w') as f:
        f.write(f"=== Price Channel Scan ===\nStarted: {datetime.now()}\n\n")
    try:
        run_price_channel_scan(log_callback=lambda m: open(LOG_FILE, 'a').write(m))
    except Exception as e:
        with open(LOG_FILE, 'a') as f:
            f.write(f"\nERROR: {e}\n")
    finally:
        with _job_lock:
            _job_running = False
            _job_name    = ''


def start_price_channel_scan():
    global _job_running, _job_name
    with _job_lock:
        if _job_running:
            return False
        _job_running = True
        _job_name    = 'Channel Scan'
    threading.Thread(target=_run_price_channel_scan_job, daemon=True).start()
    return True


@app.route('/run-channels')
def run_channels():
    if not is_admin():
        return redirect('/admin')
    start_price_channel_scan()
    return redirect('/channels')


@app.route('/channels')
def channels_page():
    if not is_admin():
        return redirect('/')

    with _job_lock:
        running = _job_running
        jname   = _job_name

    last = load_last_price_channel_results()

    if running and jname == 'Channel Scan':
        run_btn = '<span class="btn btn-off">⏳ Scanning…</span>'
    elif running:
        run_btn = '<span class="btn btn-off">Another job running</span>'
    else:
        run_btn = '<a href="/run-channels" class="btn btn-blue">▶ Run Channel Scan</a>'

    scan_info = ''
    if last:
        d = last['daily']['total']
        w = last['weekly']['total']
        m = last['monthly']['total']
        scan_info = (f"Last scan: {last['scan_date']} &nbsp;·&nbsp; "
                     f"{d} daily · {w} weekly · {m} monthly signals "
                     f"from {last['tickers_scanned']} tickers")

    def score_color(s):
        if s >= 8: return '#22c55e'
        if s >= 5: return '#f59e0b'
        return '#555'

    def dir_badge(d):
        if d == 'ascending':
            return '<span style="color:#22c55e;font-size:.78rem;font-weight:700">▲ Up</span>'
        return '<span style="color:#ef4444;font-size:.78rem;font-weight:700">▼ Dn</span>'

    def build_rows(results, tf):
        html = ''
        for r in results:
            sc = r['score']
            html += f"""
            <tr class="ch-row" data-ticker="{r['ticker']}" data-tf="{tf}">
              <td><strong style="color:#60a5fa">{r['ticker']}</strong></td>
              <td style="text-align:center">
                <span style="background:{score_color(sc)};color:#fff;padding:2px 9px;
                             border-radius:10px;font-weight:700;font-size:.82rem">{sc}</span>
              </td>
              <td style="color:#aaa">{r['ch_pct']}%</td>
              <td style="color:#aaa">{r['width_pct']}%</td>
              <td style="color:#888">{r['r2']}</td>
              <td style="color:#aaa">{r['low_touches']}L · {r['high_touches']}H</td>
              <td style="color:#fff;font-weight:600">${r['lower']:,.4f}</td>
              <td style="color:#fff;font-weight:600">${r['upper']:,.4f}</td>
              <td style="color:#fff;font-weight:600">${r['current']:,.4f}</td>
            </tr>"""
        return html or f'<tr><td colspan="9" style="color:#555;padding:16px">No signals found.</td></tr>'

    daily_rows   = build_rows(last['daily']['results'],   'daily')   if last else ''
    weekly_rows  = build_rows(last['weekly']['results'],  'weekly')  if last else ''
    monthly_rows = build_rows(last['monthly']['results'], 'monthly') if last else ''

    no_results = '<tr><td colspan="9" style="color:#555;padding:16px">No scan run yet.</td></tr>'
    if not last:
        daily_rows = weekly_rows = monthly_rows = no_results

    daily_total   = last['daily']['total']   if last else 0
    weekly_total  = last['weekly']['total']  if last else 0
    monthly_total = last['monthly']['total'] if last else 0

    def tv_box(tf_id):
        return f"""
        <div style="background:#0d0f1a;border:1px solid #1e2235;border-radius:7px;padding:10px 12px;margin-bottom:12px">
          <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:7px">
            <span style="color:#aaa;font-size:.75rem;font-weight:600;letter-spacing:.04em">TRADINGVIEW LIST</span>
            <button onclick="chCopy('{tf_id}')" id="ch-copy-{tf_id}"
              style="background:#1e3a5f;border:1px solid #3b82f6;color:#60a5fa;padding:4px 12px;
                     border-radius:5px;cursor:pointer;font-size:.75rem;font-weight:600">Copy</button>
          </div>
          <textarea id="ch-tv-{tf_id}" readonly rows="2"
            style="width:100%;background:#080a10;border:1px solid #1a1d2e;border-radius:4px;
                   color:#c7d2fe;font-size:.76rem;padding:6px 8px;resize:none;
                   font-family:monospace;box-sizing:border-box;line-height:1.5"></textarea>
        </div>"""

    def ch_table(tf_id, rows, total, sublabel):
        return f"""
        <div class="ch-tab-panel" id="ch-panel-{tf_id}">
          <p style="color:#555;font-size:.78rem;margin-bottom:10px">{sublabel} &nbsp;·&nbsp; {total} signals</p>
          {tv_box(tf_id)}
          <table class="ch-table">
            <thead><tr>
              <th onclick="chSort(this,'{tf_id}')">Ticker</th>
              <th onclick="chSort(this,'{tf_id}')" style="text-align:center">Score</th>
              <th onclick="chSort(this,'{tf_id}')">In Channel%</th>
              <th onclick="chSort(this,'{tf_id}')">Width%</th>
              <th onclick="chSort(this,'{tf_id}')">R²</th>
              <th onclick="chSort(this,'{tf_id}')">Touches</th>
              <th onclick="chSort(this,'{tf_id}')">Lower</th>
              <th onclick="chSort(this,'{tf_id}')">Upper</th>
              <th onclick="chSort(this,'{tf_id}')">Current</th>
            </tr></thead>
            <tbody id="ch-tbody-{tf_id}">
              {rows}
            </tbody>
          </table>
        </div>"""

    content = f"""
    <section style="margin-bottom:20px">
      <h2>Price Channel Scanner</h2>
      <p style="font-size:.88rem;color:#888;margin-bottom:10px">
        Ascending parallel price channels — signals when price is in the bottom 10% of
        the channel width, near the lower trendline support. Three timeframes: daily
        (short channels), weekly (medium), monthly (multi-year mega channels on log scale).
      </p>
      <div class="btn-row" style="margin-bottom:8px">{run_btn}</div>
      <p class="note">{scan_info}</p>
    </section>

    {'<section><h2>Log</h2><pre>' + get_log().replace("<","&lt;") + '</pre></section>' if running and jname == "Channel Scan" else ''}

    <section>
      <style>
        .ch-tabs {{ display:flex; gap:0; margin-bottom:0; border-bottom:1px solid #2a2d3e; }}
        .ch-tab  {{ padding:10px 22px; cursor:pointer; font-size:.85rem; color:#555;
                   border:1px solid transparent; border-bottom:none; border-radius:6px 6px 0 0;
                   background:transparent; font-weight:500; user-select:none; }}
        .ch-tab:hover {{ color:#aaa; }}
        .ch-tab.active {{ color:#60a5fa; border-color:#2a2d3e; background:#0d0f1a;
                          font-weight:600; margin-bottom:-1px; }}
        .ch-tab-panel {{ display:none; padding-top:16px; }}
        .ch-tab-panel.active {{ display:block; }}
        .ch-table {{ width:100%; border-collapse:collapse; font-size:.88rem; }}
        .ch-table th {{ text-align:left; padding:9px 12px; color:#555; font-size:.76rem;
                        border-bottom:1px solid #2a2d3e; font-weight:500;
                        cursor:pointer; user-select:none; white-space:nowrap; }}
        .ch-table th:hover {{ color:#aaa; }}
        .ch-table th.sort-asc::after  {{ content:' ▲'; font-size:.55rem; color:#60a5fa; }}
        .ch-table th.sort-desc::after {{ content:' ▼'; font-size:.55rem; color:#60a5fa; }}
        .ch-table td {{ padding:9px 12px; border-bottom:1px solid #151820; vertical-align:middle; }}
        .ch-table .ch-row:hover td {{ background:#1f2235; cursor:pointer; }}
        .ch-table .ch-row.active td {{ background:#1a2235; border-left:2px solid #60a5fa; }}
        .ch-chart-panel {{ background:#080a10; border:1px solid #1e2235; border-radius:10px;
                           padding:16px 20px; margin-bottom:20px; display:none; }}
        .ch-chart-panel.visible {{ display:block; }}
        .score-pill {{ display:inline-block; padding:2px 9px; border-radius:10px;
                       font-weight:700; font-size:.82rem; color:#fff; }}
      </style>

      <!-- Score legend -->
      <div style="display:flex;gap:16px;flex-wrap:wrap;margin-bottom:16px">
        <span style="font-size:.78rem;color:#888">
          <span style="display:inline-block;width:9px;height:9px;border-radius:50%;
                       background:#22c55e;margin-right:4px;vertical-align:middle"></span>Score 8+ — strong channel
        </span>
        <span style="font-size:.78rem;color:#888">
          <span style="display:inline-block;width:9px;height:9px;border-radius:50%;
                       background:#f59e0b;margin-right:4px;vertical-align:middle"></span>Score 5–7 — moderate
        </span>
        <span style="font-size:.78rem;color:#555">
          In Channel% = how far price is above the lower line (0% = touching the line · 10% = max signal zone)
        </span>
      </div>

      <!-- Shared chart panel -->
      <div class="ch-chart-panel" id="ch-chart-panel">
        <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:12px">
          <span style="color:#fff;font-weight:700;font-size:1.05rem" id="ch-chart-title">—</span>
          <div style="display:flex;gap:10px;align-items:center">
            <span style="color:#555;font-size:.75rem" id="ch-chart-meta"></span>
            <button onclick="closeChChart()"
              style="background:transparent;border:1px solid #2a2d3e;color:#555;padding:4px 12px;
                     border-radius:5px;cursor:pointer;font-size:.78rem">✕ Close</button>
          </div>
        </div>
        <div id="ch-chart-main" style="height:420px;background:#0a0c14;border-radius:6px"></div>
        <div id="ch-chart-vol"  style="height:60px;background:#0a0c14;border-radius:6px;margin-top:3px"></div>
      </div>

      <!-- Tabs -->
      <div class="ch-tabs">
        <div class="ch-tab active" onclick="chTab('daily')">
          Daily <span style="font-size:.75rem;color:#555;margin-left:4px">({daily_total})</span>
        </div>
        <div class="ch-tab" onclick="chTab('weekly')">
          Weekly <span style="font-size:.75rem;color:#555;margin-left:4px">({weekly_total})</span>
        </div>
        <div class="ch-tab" onclick="chTab('monthly')">
          Monthly <span style="font-size:.75rem;color:#555;margin-left:4px">({monthly_total})</span>
        </div>
      </div>

      {ch_table('daily',   daily_rows,   daily_total,   'Short channels — weeks to months')}
      {ch_table('weekly',  weekly_rows,  weekly_total,  'Medium channels — months to ~1.5 years')}
      {ch_table('monthly', monthly_rows, monthly_total, 'Mega channels — multi-year (log scale)')}
    </section>

    <script src="https://unpkg.com/lightweight-charts@4.1.3/dist/lightweight-charts.standalone.production.js"></script>
    <script>
    // ── LightweightCharts v4 VerticalLine ────────────────────────────────────
    class ChLineRenderer {{
      constructor(t,c,chart) {{ this._t=t; this._c=c; this._chart=chart; }}
      draw(target) {{
        const x=this._chart.timeScale().timeToCoordinate(this._t);
        if(x===null) return;
        target.useBitmapCoordinateSpace(scope=>{{
          const ctx=scope.context, xb=Math.round(x*scope.horizontalPixelRatio);
          ctx.save(); ctx.beginPath(); ctx.moveTo(xb,0); ctx.lineTo(xb,scope.bitmapSize.height);
          ctx.strokeStyle=this._c; ctx.lineWidth=Math.round(2*scope.horizontalPixelRatio);
          ctx.setLineDash([6,4]); ctx.stroke(); ctx.restore();
        }});
      }}
    }}
    class ChLinePaneView {{
      constructor(t,c,chart) {{ this._r=new ChLineRenderer(t,c,chart); }}
      renderer() {{ return this._r; }} zOrder() {{ return 'normal'; }}
    }}
    class ChLine {{
      constructor(t,c='#60a5fa') {{ this._t=t; this._c=c; this._chart=null; this._v=[]; }}
      attached({{chart}}) {{ this._chart=chart; this._v=[new ChLinePaneView(this._t,this._c,chart)]; }}
      detached() {{ this._v=[]; }} paneViews() {{ return this._v; }} updateAllViews() {{}}
    }}

    // ── Tab switching ────────────────────────────────────────────────────────
    function chTab(tf) {{
      document.querySelectorAll('.ch-tab').forEach((t,i) => {{
        const tfs=['daily','weekly','monthly'];
        t.classList.toggle('active', tfs[i]===tf);
      }});
      document.querySelectorAll('.ch-tab-panel').forEach(p => p.classList.remove('active'));
      const panel = document.getElementById('ch-panel-'+tf);
      if (panel) panel.classList.add('active');
      chUpdateTV(tf);
    }}

    // ── Sorting ──────────────────────────────────────────────────────────────
    function chSort(th, tf) {{
      const tbody = document.getElementById('ch-tbody-'+tf);
      if (!tbody) return;
      const idx = th.cellIndex;
      const asc = th.classList.contains('sort-desc');
      th.closest('thead').querySelectorAll('th').forEach(h => h.classList.remove('sort-asc','sort-desc'));
      th.classList.add(asc ? 'sort-asc' : 'sort-desc');
      const rows = Array.from(tbody.querySelectorAll('.ch-row'));
      rows.sort((a,b) => {{
        const av=a.cells[idx].textContent.trim(), bv=b.cells[idx].textContent.trim();
        const an=parseFloat(av.replace(/[^0-9.-]/g,'')), bn=parseFloat(bv.replace(/[^0-9.-]/g,''));
        const cmp=isNaN(an) ? av.localeCompare(bv) : an-bn;
        return asc ? cmp : -cmp;
      }});
      rows.forEach(r => tbody.appendChild(r));
    }}

    // ── TV watchlist ─────────────────────────────────────────────────────────
    function chUpdateTV(tf) {{
      const tickers=[];
      const tbody=document.getElementById('ch-tbody-'+tf);
      if (tbody) tbody.querySelectorAll('.ch-row').forEach(r => tickers.push(r.dataset.ticker));
      const ta=document.getElementById('ch-tv-'+tf);
      if (ta) ta.value = tickers.join(',');
    }}

    function chCopy(tf) {{
      const ta=document.getElementById('ch-tv-'+tf);
      const btn=document.getElementById('ch-copy-'+tf);
      if (!ta) return;
      ta.select(); ta.setSelectionRange(0,99999);
      navigator.clipboard.writeText(ta.value).then(()=>{{
        btn.textContent='Copied!'; btn.style.background='#14532d';
        btn.style.borderColor='#22c55e'; btn.style.color='#4ade80';
        setTimeout(()=>{{
          btn.textContent='Copy'; btn.style.background='#1e3a5f';
          btn.style.borderColor='#3b82f6'; btn.style.color='#60a5fa';
        }},2000);
      }});
    }}

    // ── Chart panel ──────────────────────────────────────────────────────────
    let chMainChart=null, chVolChart=null;

    function closeChChart() {{
      document.getElementById('ch-chart-panel').classList.remove('visible');
      document.querySelectorAll('.ch-row.active').forEach(r=>r.classList.remove('active'));
      if(chMainChart){{ chMainChart.remove(); chMainChart=null; }}
      if(chVolChart){{  chVolChart.remove();  chVolChart=null; }}
    }}

    function loadChChart(ticker, tf) {{
      document.getElementById('ch-chart-title').textContent=ticker+' ('+tf+')';
      document.getElementById('ch-chart-meta').textContent='Loading…';
      const panel=document.getElementById('ch-chart-panel');
      panel.classList.add('visible');
      panel.scrollIntoView({{behavior:'smooth',block:'nearest'}});
      if(chMainChart){{ chMainChart.remove(); chMainChart=null; }}
      if(chVolChart){{  chVolChart.remove();  chVolChart=null; }}
      document.getElementById('ch-chart-main').innerHTML='';
      document.getElementById('ch-chart-vol').innerHTML='';

      // Load OHLCV + channel lines in parallel
      Promise.all([
        fetch('/api/us-chart/'+ticker).then(r=>r.json()),
        fetch('/api/channel-lines/'+ticker+'/'+tf).then(r=>r.json()),
      ]).then(([data, chLines])=>{{
          if(data.error){{ document.getElementById('ch-chart-meta').textContent=data.error; return; }}
          document.getElementById('ch-chart-meta').textContent=
            data.bars+' bars · '+data.date_range
            +(chLines.r2 ? ' · Channel R²='+chLines.r2 : '');
          chMainChart=LightweightCharts.createChart(document.getElementById('ch-chart-main'),{{
            layout:{{background:{{color:'#0a0c14'}},textColor:'#888'}},
            grid:{{vertLines:{{color:'#1a1d2e'}},horzLines:{{color:'#1a1d2e'}}}},
            rightPriceScale:{{borderColor:'#2a2d3e'}},
            timeScale:{{borderColor:'#2a2d3e',timeVisible:true}},
            crosshair:{{mode:LightweightCharts.CrosshairMode.Normal}},
          }});
          const candles=chMainChart.addCandlestickSeries({{
            upColor:'#22c55e',downColor:'#ef4444',
            borderUpColor:'#22c55e',borderDownColor:'#ef4444',
            wickUpColor:'#22c55e',wickDownColor:'#ef4444',
          }});
          candles.setData(data.ohlcv);
          const ema5 =chMainChart.addLineSeries({{color:'#60a5fa',lineWidth:1,title:'EMA5'}});
          const ema26=chMainChart.addLineSeries({{color:'#f59e0b',lineWidth:1,title:'EMA26'}});
          ema5.setData(data.ema5); ema26.setData(data.ema26);

          // Draw channel lines if available
          if(chLines.lower && chLines.upper) {{
            const lowerSeries=chMainChart.addLineSeries({{
              color:'#22c55e', lineWidth:2, lineStyle:0,
              title:'Lower', priceLineVisible:false, lastValueVisible:false,
            }});
            lowerSeries.setData(chLines.lower);
            const upperSeries=chMainChart.addLineSeries({{
              color:'#3b82f6', lineWidth:2, lineStyle:0,
              title:'Upper', priceLineVisible:false, lastValueVisible:false,
            }});
            upperSeries.setData(chLines.upper);
            // Signal zone: bottom 10% of channel — shade by drawing a thin band
            // (approximate: draw a dashed line at lower + 10% of (upper-upper) offset)
            const zoneLine=chMainChart.addLineSeries({{
              color:'#22c55e55', lineWidth:1, lineStyle:2,
              priceLineVisible:false, lastValueVisible:false,
            }});
            const zoneData=chLines.lower.map((pt,i)=>{{
              const uv=chLines.upper[i]?chLines.upper[i].value:pt.value;
              return {{time:pt.time, value:pt.value+(uv-pt.value)*0.10}};
            }});
            zoneLine.setData(zoneData);
          }}

          const bc=data.ohlcv.length;
          chMainChart.timeScale().setVisibleLogicalRange({{from:Math.max(0,bc-120),to:bc+5}});
          chMainChart.priceScale('right').applyOptions({{scaleMargins:{{top:0.12,bottom:0.18}}}});
          chVolChart=LightweightCharts.createChart(document.getElementById('ch-chart-vol'),{{
            layout:{{background:{{color:'#0a0c14'}},textColor:'#888'}},
            grid:{{vertLines:{{color:'#1a1d2e'}},horzLines:{{color:'#1a1d2e'}}}},
            rightPriceScale:{{borderColor:'#2a2d3e'}},
            timeScale:{{borderColor:'#2a2d3e',timeVisible:false}},
          }});
          const vs=chVolChart.addHistogramSeries({{priceFormat:{{type:'volume'}},priceScaleId:''}});
          vs.priceScale().applyOptions({{scaleMargins:{{top:0.1,bottom:0}}}});
          vs.setData(data.volume); chVolChart.timeScale().fitContent();
          chMainChart.timeScale().subscribeVisibleLogicalRangeChange(r=>chVolChart.timeScale().setVisibleLogicalRange(r));
          chVolChart.timeScale().subscribeVisibleLogicalRangeChange(r=>chMainChart.timeScale().setVisibleLogicalRange(r));
        }})
        .catch(e=>{{ document.getElementById('ch-chart-meta').textContent='Failed: '+e; }});
    }}

    // ── Row click ────────────────────────────────────────────────────────────
    document.querySelectorAll('.ch-row').forEach(row=>{{
      row.addEventListener('click',()=>{{
        const isActive=row.classList.contains('active');
        document.querySelectorAll('.ch-row.active').forEach(r=>r.classList.remove('active'));
        if(isActive){{ closeChChart(); return; }}
        row.classList.add('active');
        loadChChart(row.dataset.ticker, row.dataset.tf);
      }});
    }});

    // ── Init ─────────────────────────────────────────────────────────────────
    chTab('daily');
    </script>"""

    return page_wrap('Channel Scanner', 'channels', content, auto_refresh=(running and jname == 'Channel Scan'))


# ─── Jang's Wicks ─────────────────────────────────────────────────────────────

@app.route('/jangs-wicks/run-daily')
def jangs_run_daily():
    if not current_user_id() and not is_admin():
        return redirect('/ask/login')
    start_hammer_scan()
    return redirect('/jangs-wicks')


@app.route('/jangs-wicks/run-weekly')
def jangs_run_weekly():
    if not current_user_id() and not is_admin():
        return redirect('/ask/login')
    start_wick_scan()
    return redirect('/jangs-wicks')


@app.route('/jangs-wicks')
def jangs_wicks_page():
    daily   = load_last_hammer_results()
    weekly  = load_last_wick_results()
    logged_in = current_user_id() or is_admin()

    with _job_lock:
        running = _job_running
        jname   = _job_name

    def score_color(s):
        if s >= 8: return '#22c55e'
        if s >= 5: return '#f59e0b'
        return '#555'

    # ── Daily hammer rows ──────────────────────────────────────────────────────
    daily_rows = ''
    if daily and daily.get('results'):
        for r in daily['results']:
            sc  = r['score']
            gc  = '#22c55e' if r['gain_pct'] >= 0 else '#ef4444'
            gs  = '+' if r['gain_pct'] >= 0 else ''
            bull = '▲' if r.get('bullish') else '▽'
            bc   = '#22c55e' if r.get('bullish') else '#ef4444'
            vol  = ' ⚡' if r.get('vol_surge') else ''
            daily_rows += f"""
            <tr class="jw-row" data-ticker="{r['ticker']}" data-date="{r['hammer_date']}" data-side="daily">
              <td><strong style="color:#60a5fa">{r['ticker']}</strong></td>
              <td style="color:#aaa;font-size:.82rem">{r['hammer_date']}</td>
              <td style="text-align:center">
                <span style="background:{score_color(sc)};color:#fff;padding:2px 9px;
                             border-radius:10px;font-weight:700;font-size:.82rem">{sc}</span>
              </td>
              <td style="color:#fff;font-weight:600">{r['wick_ratio']}×</td>
              <td style="color:#888">{r['close_pct']}%</td>
              <td style="color:{bc};font-weight:600;font-size:.82rem">{bull}{vol}</td>
              <td style="color:{gc};font-weight:700">{gs}{r['gain_pct']:.2f}%</td>
            </tr>"""

    # ── Weekly wick rows ───────────────────────────────────────────────────────
    weekly_rows = ''
    if weekly and weekly.get('results'):
        for r in weekly['results']:
            sc  = r['score']
            gc  = '#22c55e' if r['gain_pct'] >= 0 else '#ef4444'
            gs  = '+' if r['gain_pct'] >= 0 else ''
            weekly_rows += f"""
            <tr class="jw-row" data-ticker="{r['ticker']}" data-date="{r['wick_date']}" data-side="weekly">
              <td><strong style="color:#60a5fa">{r['ticker']}</strong></td>
              <td style="color:#aaa;font-size:.82rem">{r['wick_date']}</td>
              <td style="text-align:center">
                <span style="background:{score_color(sc)};color:#fff;padding:2px 9px;
                             border-radius:10px;font-weight:700;font-size:.82rem">{sc}</span>
              </td>
              <td style="color:#fff;font-weight:600">{r['wick_ratio']}×</td>
              <td style="color:#aaa">{r['weeks_held']}w</td>
              <td style="color:#888">{r['close_pct']}%</td>
              <td style="color:{gc};font-weight:700">{gs}{r['gain_pct']:.2f}%</td>
            </tr>"""

    daily_info  = f"{daily['scan_date']} · {daily['total']} signals"   if daily  else 'No scan yet'
    weekly_info = f"{weekly['scan_date']} · {weekly['total']} signals"  if weekly else 'No scan yet'

    content = f"""
    <style>
      .jw-grid {{ display:grid; grid-template-columns:1fr 1fr; gap:20px; margin-bottom:24px; }}
      @media(max-width:900px) {{ .jw-grid {{ grid-template-columns:1fr; }} }}
      .jw-card {{ background:#0d0f1a; border:1px solid #1e2235; border-radius:10px; padding:16px; }}
      .jw-card h3 {{ font-size:.72rem; font-weight:700; color:#777; text-transform:uppercase;
                    letter-spacing:.08em; margin-bottom:12px; }}
      .jw-table {{ width:100%; border-collapse:collapse; font-size:.88rem; }}
      .jw-table th {{ text-align:left; padding:8px 10px; color:#555; font-size:.74rem;
                     border-bottom:1px solid #2a2d3e; font-weight:500;
                     cursor:pointer; user-select:none; white-space:nowrap; }}
      .jw-table th:hover {{ color:#aaa; }}
      .jw-table th.sort-asc::after  {{ content:' ▲'; font-size:.55rem; color:#60a5fa; }}
      .jw-table th.sort-desc::after {{ content:' ▼'; font-size:.55rem; color:#60a5fa; }}
      .jw-table td {{ padding:8px 10px; border-bottom:1px solid #151820; vertical-align:middle; }}
      .jw-table .jw-row:hover td {{ background:#1f2235; cursor:pointer; }}
      .jw-table .jw-row.active td {{ background:#1a2235; border-left:2px solid #f59e0b; }}
      .jw-filter-btn {{ background:#1a1d2e; border:1px solid #2a2d3e; color:#888;
                        padding:5px 13px; border-radius:6px; cursor:pointer; font-size:.78rem; }}
      .jw-filter-btn.active {{ background:#1e3a5f; border-color:#3b82f6; color:#60a5fa; font-weight:600; }}
      .jw-tv-box {{ background:#0d0f1a; border:1px solid #1e2235; border-radius:7px;
                   padding:10px 12px; margin-bottom:10px; }}
      .jw-chart-panel {{ background:#080a10; border:1px solid #1e2235; border-radius:10px;
                         padding:16px 20px; margin-bottom:24px; display:none; }}
      .jw-chart-panel.visible {{ display:block; }}
      .score-legend {{ display:flex; gap:14px; flex-wrap:wrap; margin-bottom:14px; }}
      .score-legend span {{ font-size:.75rem; color:#888; }}
      .score-legend .dot {{ display:inline-block; width:10px; height:10px; border-radius:50%;
                            margin-right:4px; vertical-align:middle; }}
    </style>

    <section style="margin-bottom:20px">
      <h2 style="margin-bottom:4px">Jang's Wicks</h2>
      <p style="font-size:.88rem;color:#555;margin-bottom:14px">
        Daily and weekly wick signals — click any ticker to load the chart.
      </p>
      {'<div class="btn-row" style="margin-bottom:14px">' + (
          '<span class="btn btn-off">⏳ ' + jname + ' running…</span>'
          if running else
          '<a href="/jangs-wicks/run-daily" class="btn btn-blue">▶ Run Daily Scan</a>'
          '<a href="/jangs-wicks/run-weekly" class="btn btn-blue">▶ Run Weekly Scan</a>'
      ) + '</div>' if logged_in else
      '<p style="font-size:.82rem;color:#555;margin-bottom:14px"><a href="/ask/login" style="color:#60a5fa">Log in</a> to run scans.</p>'}
      <div class="score-legend">
        <span><span class="dot" style="background:#22c55e"></span>Score 8+ — strong signal</span>
        <span><span class="dot" style="background:#f59e0b"></span>Score 5–7 — moderate signal</span>
        <span><span class="dot" style="background:#555"></span>Score &lt;5 — weak signal</span>
        <span style="color:#444">⚡ = above-average volume &nbsp;·&nbsp; ▲ = bullish close &nbsp;·&nbsp; ▽ = bearish close</span>
      </div>
    </section>

    <!-- Chart panel (shared, full-width) -->
    <div class="jw-chart-panel" id="jw-chart-panel">
      <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:12px">
        <span style="color:#fff;font-weight:700;font-size:1.05rem" id="jw-chart-title">—</span>
        <div style="display:flex;gap:10px;align-items:center">
          <span style="color:#555;font-size:.75rem" id="jw-chart-meta"></span>
          <button onclick="closeJwChart()"
            style="background:transparent;border:1px solid #2a2d3e;color:#555;padding:4px 12px;
                   border-radius:5px;cursor:pointer;font-size:.78rem">✕ Close</button>
        </div>
      </div>
      <div id="jw-chart-main" style="height:400px;background:#0a0c14;border-radius:6px"></div>
      <div id="jw-chart-vol"  style="height:60px;background:#0a0c14;border-radius:6px;margin-top:3px"></div>
    </div>

    <div class="jw-grid">

      <!-- ── Daily Hammers ── -->
      <div class="jw-card">
        <h3>Daily Close Hammers</h3>
        <p style="color:#555;font-size:.75rem;margin-bottom:10px">{daily_info}</p>

        <div class="jw-tv-box">
          <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:7px">
            <span style="color:#aaa;font-size:.75rem;font-weight:600;letter-spacing:.04em">TRADINGVIEW LIST</span>
            <button onclick="copyJwList('daily')" id="jw-copy-daily"
              style="background:#1e3a5f;border:1px solid #3b82f6;color:#60a5fa;padding:4px 12px;
                     border-radius:5px;cursor:pointer;font-size:.75rem;font-weight:600">Copy</button>
          </div>
          <textarea id="jw-tv-daily" readonly rows="2"
            style="width:100%;background:#080a10;border:1px solid #1a1d2e;border-radius:4px;
                   color:#c7d2fe;font-size:.76rem;padding:6px 8px;resize:none;
                   font-family:monospace;box-sizing:border-box;line-height:1.5"></textarea>
        </div>

        <div style="display:flex;align-items:center;gap:7px;margin-bottom:10px">
          <button class="jw-filter-btn active" id="jw-df-today" onclick="jwFilter('daily','today')">Today</button>
          <button class="jw-filter-btn"         id="jw-df-all"   onclick="jwFilter('daily','all')">All</button>
          <span id="jw-daily-count" style="color:#555;font-size:.75rem;margin-left:4px"></span>
        </div>

        <table class="jw-table" id="jw-daily-tbl">
          <thead><tr>
            <th onclick="jwSort(this,'daily')">Ticker</th>
            <th onclick="jwSort(this,'daily')">Date</th>
            <th onclick="jwSort(this,'daily')" style="text-align:center">Score</th>
            <th onclick="jwSort(this,'daily')">Wick×</th>
            <th onclick="jwSort(this,'daily')">Close%</th>
            <th onclick="jwSort(this,'daily')">Body</th>
            <th onclick="jwSort(this,'daily')">Gain</th>
          </tr></thead>
          <tbody id="jw-daily-tbody">
            {daily_rows if daily_rows else '<tr><td colspan="7" style="color:#555;padding:16px">No scan results yet.</td></tr>'}
          </tbody>
        </table>
      </div>

      <!-- ── Weekly Wicks ── -->
      <div class="jw-card">
        <h3>Weekly Close Wicks</h3>
        <p style="color:#555;font-size:.75rem;margin-bottom:10px">{weekly_info}</p>

        <div class="jw-tv-box">
          <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:7px">
            <span style="color:#aaa;font-size:.75rem;font-weight:600;letter-spacing:.04em">TRADINGVIEW LIST</span>
            <button onclick="copyJwList('weekly')" id="jw-copy-weekly"
              style="background:#1e3a5f;border:1px solid #3b82f6;color:#60a5fa;padding:4px 12px;
                     border-radius:5px;cursor:pointer;font-size:.75rem;font-weight:600">Copy</button>
          </div>
          <textarea id="jw-tv-weekly" readonly rows="2"
            style="width:100%;background:#080a10;border:1px solid #1a1d2e;border-radius:4px;
                   color:#c7d2fe;font-size:.76rem;padding:6px 8px;resize:none;
                   font-family:monospace;box-sizing:border-box;line-height:1.5"></textarea>
        </div>

        <div style="display:flex;align-items:center;gap:7px;margin-bottom:10px">
          <button class="jw-filter-btn active" id="jw-wf-week" onclick="jwFilter('weekly','week')">Last Week</button>
          <button class="jw-filter-btn"         id="jw-wf-all"  onclick="jwFilter('weekly','all')">All</button>
          <span id="jw-weekly-count" style="color:#555;font-size:.75rem;margin-left:4px"></span>
        </div>

        <table class="jw-table" id="jw-weekly-tbl">
          <thead><tr>
            <th onclick="jwSort(this,'weekly')">Ticker</th>
            <th onclick="jwSort(this,'weekly')">Date</th>
            <th onclick="jwSort(this,'weekly')" style="text-align:center">Score</th>
            <th onclick="jwSort(this,'weekly')">Wick×</th>
            <th onclick="jwSort(this,'weekly')">Held</th>
            <th onclick="jwSort(this,'weekly')">Close%</th>
            <th onclick="jwSort(this,'weekly')">Gain</th>
          </tr></thead>
          <tbody id="jw-weekly-tbody">
            {weekly_rows if weekly_rows else '<tr><td colspan="7" style="color:#555;padding:16px">No scan results yet.</td></tr>'}
          </tbody>
        </table>
      </div>

    </div><!-- /.jw-grid -->

    <script src="https://unpkg.com/lightweight-charts@4.1.3/dist/lightweight-charts.standalone.production.js"></script>
    <script>
    // ── LightweightCharts v4 VerticalLine primitive ──────────────────────────
    class JwLineRenderer {{
      constructor(time, color, chart) {{ this._time=time; this._color=color; this._chart=chart; }}
      draw(target) {{
        const x = this._chart.timeScale().timeToCoordinate(this._time);
        if (x === null) return;
        target.useBitmapCoordinateSpace(scope => {{
          const ctx=scope.context, xb=Math.round(x*scope.horizontalPixelRatio);
          ctx.save(); ctx.beginPath(); ctx.moveTo(xb,0); ctx.lineTo(xb,scope.bitmapSize.height);
          ctx.strokeStyle=this._color; ctx.lineWidth=Math.round(2*scope.horizontalPixelRatio);
          ctx.setLineDash([6,4]); ctx.stroke(); ctx.restore();
        }});
      }}
    }}
    class JwLinePaneView {{
      constructor(t,c,chart) {{ this._r=new JwLineRenderer(t,c,chart); }}
      renderer() {{ return this._r; }} zOrder() {{ return 'normal'; }}
    }}
    class JwLine {{
      constructor(time,color='#f59e0b') {{ this._time=time; this._color=color; this._chart=null; this._views=[]; }}
      attached({{chart}}) {{ this._chart=chart; this._views=[new JwLinePaneView(this._time,this._color,chart)]; }}
      detached() {{ this._views=[]; }} paneViews() {{ return this._views; }} updateAllViews() {{}}
    }}

    // ── Chart state ──────────────────────────────────────────────────────────
    let jwMainChart=null, jwVolChart=null;

    function closeJwChart() {{
      document.getElementById('jw-chart-panel').classList.remove('visible');
      document.querySelectorAll('.jw-row.active').forEach(r => r.classList.remove('active'));
      if (jwMainChart) {{ jwMainChart.remove(); jwMainChart=null; }}
      if (jwVolChart)  {{ jwVolChart.remove();  jwVolChart=null; }}
    }}

    function loadJwChart(ticker, signalDate) {{
      document.getElementById('jw-chart-title').textContent = ticker;
      document.getElementById('jw-chart-meta').textContent  = 'Loading…';
      const panel = document.getElementById('jw-chart-panel');
      panel.classList.add('visible');
      panel.scrollIntoView({{behavior:'smooth', block:'nearest'}});

      if (jwMainChart) {{ jwMainChart.remove(); jwMainChart=null; }}
      if (jwVolChart)  {{ jwVolChart.remove();  jwVolChart=null; }}
      document.getElementById('jw-chart-main').innerHTML = '';
      document.getElementById('jw-chart-vol').innerHTML  = '';

      fetch('/api/us-chart/' + ticker)
        .then(r => r.json())
        .then(data => {{
          if (data.error) {{ document.getElementById('jw-chart-meta').textContent=data.error; return; }}
          document.getElementById('jw-chart-meta').textContent = data.bars+' bars · '+data.date_range;

          jwMainChart = LightweightCharts.createChart(document.getElementById('jw-chart-main'), {{
            layout: {{background:{{color:'#0a0c14'}}, textColor:'#888'}},
            grid: {{vertLines:{{color:'#1a1d2e'}}, horzLines:{{color:'#1a1d2e'}}}},
            rightPriceScale: {{borderColor:'#2a2d3e'}},
            timeScale: {{borderColor:'#2a2d3e', timeVisible:true}},
            crosshair: {{mode:LightweightCharts.CrosshairMode.Normal}},
          }});
          const candles = jwMainChart.addCandlestickSeries({{
            upColor:'#22c55e', downColor:'#ef4444',
            borderUpColor:'#22c55e', borderDownColor:'#ef4444',
            wickUpColor:'#22c55e', wickDownColor:'#ef4444',
          }});
          candles.setData(data.ohlcv);

          // Snap to nearest bar to signal date
          const sigMs = new Date(signalDate).getTime();
          let snapDate=signalDate, minDiff=Infinity;
          for (const bar of data.ohlcv) {{
            const diff = Math.abs(new Date(bar.time).getTime()-sigMs);
            if (diff<minDiff) {{ minDiff=diff; snapDate=bar.time; }}
          }}
          candles.attachPrimitive(new JwLine(snapDate));

          const ema5  = jwMainChart.addLineSeries({{color:'#60a5fa', lineWidth:1, title:'EMA5'}});
          const ema26 = jwMainChart.addLineSeries({{color:'#f59e0b', lineWidth:1, title:'EMA26'}});
          ema5.setData(data.ema5); ema26.setData(data.ema26);

          const bc = data.ohlcv.length;
          jwMainChart.timeScale().setVisibleLogicalRange({{from:Math.max(0,bc-120), to:bc+5}});
          jwMainChart.priceScale('right').applyOptions({{scaleMargins:{{top:0.12, bottom:0.18}}}});

          jwVolChart = LightweightCharts.createChart(document.getElementById('jw-chart-vol'), {{
            layout: {{background:{{color:'#0a0c14'}}, textColor:'#888'}},
            grid: {{vertLines:{{color:'#1a1d2e'}}, horzLines:{{color:'#1a1d2e'}}}},
            rightPriceScale: {{borderColor:'#2a2d3e'}},
            timeScale: {{borderColor:'#2a2d3e', timeVisible:false}},
          }});
          const vs = jwVolChart.addHistogramSeries({{priceFormat:{{type:'volume'}}, priceScaleId:''}});
          vs.priceScale().applyOptions({{scaleMargins:{{top:0.1, bottom:0}}}});
          vs.setData(data.volume); jwVolChart.timeScale().fitContent();

          jwMainChart.timeScale().subscribeVisibleLogicalRangeChange(r => jwVolChart.timeScale().setVisibleLogicalRange(r));
          jwVolChart.timeScale().subscribeVisibleLogicalRangeChange(r => jwMainChart.timeScale().setVisibleLogicalRange(r));
        }})
        .catch(e => {{ document.getElementById('jw-chart-meta').textContent='Failed: '+e; }});
    }}

    // ── Row click ────────────────────────────────────────────────────────────
    document.querySelectorAll('.jw-row').forEach(row => {{
      row.addEventListener('click', () => {{
        const isActive = row.classList.contains('active');
        document.querySelectorAll('.jw-row.active').forEach(r => r.classList.remove('active'));
        if (isActive) {{ closeJwChart(); return; }}
        row.classList.add('active');
        loadJwChart(row.dataset.ticker, row.dataset.date);
      }});
    }});

    // ── Sorting ──────────────────────────────────────────────────────────────
    function jwSort(th, side) {{
      const tbodyId = side==='daily' ? 'jw-daily-tbody' : 'jw-weekly-tbody';
      const tbody = document.getElementById(tbodyId);
      const idx = th.cellIndex;
      const asc = th.classList.contains('sort-desc');
      th.closest('thead').querySelectorAll('th').forEach(h => h.classList.remove('sort-asc','sort-desc'));
      th.classList.add(asc ? 'sort-asc' : 'sort-desc');
      const rows = Array.from(tbody.querySelectorAll('.jw-row'));
      rows.sort((a,b) => {{
        const av=a.cells[idx].textContent.trim(), bv=b.cells[idx].textContent.trim();
        const an=parseFloat(av.replace(/[^0-9.-]/g,'')), bn=parseFloat(bv.replace(/[^0-9.-]/g,''));
        const cmp=isNaN(an) ? av.localeCompare(bv) : an-bn;
        return asc ? cmp : -cmp;
      }});
      rows.forEach(r => tbody.appendChild(r));
    }}

    // ── Filter ───────────────────────────────────────────────────────────────
    function getLatestDate(side) {{
      let latest='';
      document.querySelectorAll(`.jw-row[data-side="${{side}}"]`).forEach(r => {{
        const d=r.dataset.date||''; if(d>latest) latest=d;
      }});
      return latest;
    }}

    function jwFilter(side, mode) {{
      const isDaily = side==='daily';
      if (isDaily) {{
        document.getElementById('jw-df-today').classList.toggle('active', mode==='today');
        document.getElementById('jw-df-all').classList.toggle('active',   mode==='all');
      }} else {{
        document.getElementById('jw-wf-week').classList.toggle('active', mode==='week');
        document.getElementById('jw-wf-all').classList.toggle('active',  mode==='all');
      }}
      const latest = getLatestDate(side);
      const countId = isDaily ? 'jw-daily-count' : 'jw-weekly-count';
      let visible=0;
      document.querySelectorAll(`.jw-row[data-side="${{side}}"]`).forEach(r => {{
        const show = (mode==='all') || (r.dataset.date===latest);
        r.style.display = show ? '' : 'none';
        if (show) visible++;
        if (!show && r.classList.contains('active')) closeJwChart();
      }});
      document.getElementById(countId).textContent = visible+' signal'+(visible!==1?'s':'');
      jwUpdateTVList(side);
    }}

    // ── TV list ──────────────────────────────────────────────────────────────
    function jwUpdateTVList(side) {{
      const tickers=[];
      document.querySelectorAll(`.jw-row[data-side="${{side}}"]`).forEach(r => {{
        if (r.style.display!=='none') tickers.push(r.dataset.ticker);
      }});
      document.getElementById(side==='daily' ? 'jw-tv-daily' : 'jw-tv-weekly').value = tickers.join(',');
    }}

    function copyJwList(side) {{
      const taId = side==='daily' ? 'jw-tv-daily' : 'jw-tv-weekly';
      const btnId = side==='daily' ? 'jw-copy-daily' : 'jw-copy-weekly';
      const ta = document.getElementById(taId);
      ta.select(); ta.setSelectionRange(0,99999);
      navigator.clipboard.writeText(ta.value).then(() => {{
        const btn=document.getElementById(btnId);
        btn.textContent='Copied!'; btn.style.background='#14532d';
        btn.style.borderColor='#22c55e'; btn.style.color='#4ade80';
        setTimeout(()=>{{
          btn.textContent='Copy'; btn.style.background='#1e3a5f';
          btn.style.borderColor='#3b82f6'; btn.style.color='#60a5fa';
        }},2000);
      }});
    }}

    // ── Init ─────────────────────────────────────────────────────────────────
    jwFilter('daily',  'today');
    jwFilter('weekly', 'week');
    </script>"""

    return page_wrap("Jang's Wicks", 'jangs-wicks', content, auto_refresh=(running and jname in ('Hammer Scan','Wick Scan')))


# ─── Semiconductors ───────────────────────────────────────────────────────────

SEMIS = [
    # Large cap / equipment
    'NVDA', 'AMD', 'INTC', 'AVGO', 'QCOM', 'AMAT', 'LRCX', 'KLAC',
    'ASML', 'MU',  'TXN',  'ADI',  'MCHP', 'MRVL', 'ON',   'MPWR',
    # Mid cap
    'SWKS', 'ENTG', 'AMKR', 'NXPI', 'WOLF', 'ACLS', 'ONTO', 'CRUS',
    'SLAB', 'AMBA', 'ALGM', 'DIOD', 'LSCC', 'RMBS', 'UCTT', 'COHU',
    # Small cap / user picks
    'NVST', 'INDI', 'SMTC', 'GCTS', 'QRVO', 'AOSL', 'CEVA', 'MRAM',
    'AIP',  'QUIK', 'PLAB',
]

SEMI_NAMES = {
    'NVDA': 'NVIDIA',           'AMD':  'Advanced Micro Devices',
    'INTC': 'Intel',            'AVGO': 'Broadcom',
    'QCOM': 'Qualcomm',         'AMAT': 'Applied Materials',
    'LRCX': 'Lam Research',     'KLAC': 'KLA Corp',
    'ASML': 'ASML',             'MU':   'Micron Technology',
    'TXN':  'Texas Instruments','ADI':  'Analog Devices',
    'MCHP': 'Microchip Tech',   'MRVL': 'Marvell Technology',
    'ON':   'ON Semiconductor', 'MPWR': 'Monolithic Power',
    'SWKS': 'Skyworks',         'ENTG': 'Entegris',
    'AMKR': 'Amkor Technology', 'NXPI': 'NXP Semiconductors',
    'WOLF': 'Wolfspeed',        'ACLS': 'Axcelis Technologies',
    'ONTO': 'Onto Innovation',  'CRUS': 'Cirrus Logic',
    'SLAB': 'Silicon Labs',     'AMBA': 'Ambarella',
    'ALGM': 'Allegro MicroSystems','DIOD':'Diodes Inc',
    'LSCC': 'Lattice Semi',     'RMBS': 'Rambus',
    'UCTT': 'Ultra Clean',      'COHU': 'Cohu',
    'NVST': 'Envista Holdings', 'INDI': 'Indie Semiconductor',
    'SMTC': 'Semtech',          'GCTS': 'GCT Semiconductor',
    'QRVO': 'Qorvo',            'AOSL': 'Alpha & Omega Semi',
    'CEVA': 'CEVA Inc',         'MRAM': 'Everspin Technologies',
    'AIP':  'Arteris',          'QUIK': 'QuickLogic',
    'PLAB': 'Photronics',
}


def _get_semi_prices():
    """Return {ticker: (current_price, prev_price, volume)} for all SEMIS."""
    import pymysql
    conn = pymysql.connect(
        host=DB_HOST, user=DB_USER, password=DB_PASSWORD,
        database=DB_NAME, port=DB_PORT, charset='utf8mb4'
    )
    result = {}
    try:
        fmt = ','.join(['%s'] * len(SEMIS))
        with conn.cursor() as cur:
            cur.execute(f"""
                SELECT ticker, date, close, volume FROM prices
                WHERE ticker IN ({fmt})
                AND date >= DATE_SUB(CURDATE(), INTERVAL 10 DAY)
                ORDER BY ticker, date DESC
            """, SEMIS)
            rows = cur.fetchall()
        grouped = {}
        for ticker, date, close, vol in rows:
            grouped.setdefault(ticker, []).append((float(close), int(vol or 0)))
        for ticker, vals in grouped.items():
            cur_p  = vals[0][0]
            prev_p = vals[1][0] if len(vals) > 1 else cur_p
            cur_v  = vals[0][1]
            result[ticker] = (cur_p, prev_p, cur_v)
    finally:
        conn.close()
    return result


@app.route('/semiconductors')
def semiconductors_page():
    prices = _get_semi_prices()

    rows_html = ''
    for ticker in SEMIS:
        if ticker not in prices:
            continue
        cur_p, prev_p, vol = prices[ticker]
        chg     = (cur_p - prev_p) / prev_p * 100 if prev_p else 0
        chg_col = '#22c55e' if chg >= 0 else '#ef4444'
        chg_pfx = '+' if chg >= 0 else ''
        vol_fmt = f'{vol/1_000_000:.1f}M' if vol >= 1_000_000 else f'{vol/1_000:.0f}K'
        name    = SEMI_NAMES.get(ticker, '')
        rows_html += f"""
        <tr class="semi-row" data-ticker="{ticker}">
          <td><strong style="color:#60a5fa;font-size:.95rem">{ticker}</strong></td>
          <td style="color:#888;font-size:.82rem">{name}</td>
          <td style="color:#fff;font-weight:600">${cur_p:,.2f}</td>
          <td style="color:{chg_col};font-weight:700">{chg_pfx}{chg:.2f}%</td>
          <td style="color:#555;font-size:.82rem">{vol_fmt}</td>
        </tr>"""

    tv_list = ','.join(t for t in SEMIS if t in prices)

    content = f"""
    <style>
      .semi-table {{ width:100%; border-collapse:collapse; font-size:.9rem; }}
      .semi-table th {{ text-align:left; padding:9px 14px; color:#555; font-size:.76rem;
                       border-bottom:1px solid #2a2d3e; font-weight:500;
                       cursor:pointer; user-select:none; white-space:nowrap; }}
      .semi-table th:hover {{ color:#aaa; }}
      .semi-table th.sort-asc::after  {{ content:' ▲'; font-size:.55rem; color:#60a5fa; }}
      .semi-table th.sort-desc::after {{ content:' ▼'; font-size:.55rem; color:#60a5fa; }}
      .semi-table td {{ padding:9px 14px; border-bottom:1px solid #151820; vertical-align:middle; }}
      .semi-table .semi-row:hover td {{ background:#1f2235; cursor:pointer; }}
      .semi-table .semi-row.active td {{ background:#1a2235; border-left:2px solid #60a5fa; }}
      .semi-drop td {{ padding:0 !important; border-bottom:2px solid #2a2d3e !important; }}
    </style>

    <section style="margin-bottom:20px">
      <h2 style="margin-bottom:4px">Semiconductors</h2>
      <p style="font-size:.88rem;color:#555;margin-bottom:16px">
        {len([t for t in SEMIS if t in prices])} stocks — click any row to load the chart.
      </p>
    </section>

    <section>
      <div style="background:#0d0f1a;border:1px solid #1e2235;border-radius:8px;padding:12px 14px;margin-bottom:16px">
        <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:8px">
          <span style="color:#aaa;font-size:.75rem;font-weight:600;letter-spacing:.04em">TRADINGVIEW WATCHLIST</span>
          <button onclick="semiCopy()" id="semi-copy-btn"
            style="background:#1e3a5f;border:1px solid #3b82f6;color:#60a5fa;padding:4px 12px;
                   border-radius:5px;cursor:pointer;font-size:.75rem;font-weight:600">Copy</button>
        </div>
        <textarea id="semi-tv-list" readonly rows="2"
          style="width:100%;background:#080a10;border:1px solid #1a1d2e;border-radius:4px;
                 color:#c7d2fe;font-size:.76rem;padding:6px 8px;resize:none;
                 font-family:monospace;box-sizing:border-box;line-height:1.5">{tv_list}</textarea>
      </div>

      <table class="semi-table">
        <thead><tr>
          <th onclick="semiSort(this)">Ticker</th>
          <th onclick="semiSort(this)">Company</th>
          <th onclick="semiSort(this)">Price</th>
          <th onclick="semiSort(this)">Day %</th>
          <th onclick="semiSort(this)">Volume</th>
        </tr></thead>
        <tbody id="semi-tbody">
          {rows_html if rows_html else '<tr><td colspan="5" style="color:#555;padding:20px">No price data found.</td></tr>'}
        </tbody>
      </table>
    </section>

    <script src="https://unpkg.com/lightweight-charts@4.1.3/dist/lightweight-charts.standalone.production.js"></script>
    <script>
    // ── LightweightCharts v4 primitives ──────────────────────────────────────
    class SLRenderer {{
      constructor(t,c,chart) {{ this._t=t; this._c=c; this._chart=chart; }}
      draw(target) {{
        const x=this._chart.timeScale().timeToCoordinate(this._t);
        if(x===null) return;
        target.useBitmapCoordinateSpace(scope=>{{
          const ctx=scope.context, xb=Math.round(x*scope.horizontalPixelRatio);
          ctx.save(); ctx.beginPath(); ctx.moveTo(xb,0); ctx.lineTo(xb,scope.bitmapSize.height);
          ctx.strokeStyle=this._c; ctx.lineWidth=Math.round(2*scope.horizontalPixelRatio);
          ctx.setLineDash([6,4]); ctx.stroke(); ctx.restore();
        }});
      }}
    }}
    class SLPaneView {{
      constructor(t,c,chart) {{ this._r=new SLRenderer(t,c,chart); }}
      renderer() {{ return this._r; }} zOrder() {{ return 'normal'; }}
    }}
    class SemiLine {{
      constructor(t,c='#60a5fa') {{ this._t=t; this._c=c; this._chart=null; this._v=[]; }}
      attached({{chart}}) {{ this._chart=chart; this._v=[new SLPaneView(this._t,this._c,chart)]; }}
      detached() {{ this._v=[]; }} paneViews() {{ return this._v; }} updateAllViews() {{}}
    }}

    // ── Row click — inline drop-down chart ───────────────────────────────────
    document.querySelectorAll('.semi-row').forEach(row => {{
      row.addEventListener('click', () => {{
        const ticker  = row.dataset.ticker;
        const dropId  = 'sdrop-' + ticker;
        const exist   = document.getElementById(dropId);
        if (exist) {{ exist.remove(); row.classList.remove('active'); return; }}
        document.querySelectorAll('.semi-drop').forEach(d => d.remove());
        document.querySelectorAll('.semi-row.active').forEach(r => r.classList.remove('active'));
        row.classList.add('active');

        const drop = document.createElement('tr');
        drop.id = dropId; drop.className = 'semi-drop';
        drop.innerHTML = `<td colspan="5" style="background:#080a10;padding:16px 20px">
          <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:10px">
            <span style="color:#fff;font-weight:700;font-size:1rem">${{ticker}}</span>
            <span style="color:#555;font-size:.75rem" id="smeta-${{ticker}}">Loading…</span>
          </div>
          <div id="smain-${{ticker}}" style="height:420px;background:#0a0c14;border-radius:6px"></div>
          <div id="svol-${{ticker}}"  style="height:60px;background:#0a0c14;border-radius:6px;margin-top:3px"></div>
        </td>`;
        row.parentNode.insertBefore(drop, row.nextSibling);

        fetch('/api/us-chart/' + ticker)
          .then(r => r.json())
          .then(data => {{
            if (data.error) {{ document.getElementById('smeta-'+ticker).textContent=data.error; return; }}
            document.getElementById('smeta-'+ticker).textContent=data.bars+' bars · '+data.date_range;
            const chart = LightweightCharts.createChart(document.getElementById('smain-'+ticker), {{
              layout:{{background:{{color:'#0a0c14'}},textColor:'#888'}},
              grid:{{vertLines:{{color:'#1a1d2e'}},horzLines:{{color:'#1a1d2e'}}}},
              rightPriceScale:{{borderColor:'#2a2d3e'}},
              timeScale:{{borderColor:'#2a2d3e',timeVisible:true}},
              crosshair:{{mode:LightweightCharts.CrosshairMode.Normal}},
            }});
            const candles = chart.addCandlestickSeries({{
              upColor:'#22c55e',downColor:'#ef4444',
              borderUpColor:'#22c55e',borderDownColor:'#ef4444',
              wickUpColor:'#22c55e',wickDownColor:'#ef4444',
            }});
            candles.setData(data.ohlcv);
            const ema5  = chart.addLineSeries({{color:'#60a5fa',lineWidth:1,title:'EMA5'}});
            const ema26 = chart.addLineSeries({{color:'#f59e0b',lineWidth:1,title:'EMA26'}});
            ema5.setData(data.ema5); ema26.setData(data.ema26);
            const bc = data.ohlcv.length;
            chart.timeScale().setVisibleLogicalRange({{from:Math.max(0,bc-120),to:bc+5}});
            chart.priceScale('right').applyOptions({{scaleMargins:{{top:0.12,bottom:0.18}}}});
            const vc = LightweightCharts.createChart(document.getElementById('svol-'+ticker), {{
              layout:{{background:{{color:'#0a0c14'}},textColor:'#888'}},
              grid:{{vertLines:{{color:'#1a1d2e'}},horzLines:{{color:'#1a1d2e'}}}},
              rightPriceScale:{{borderColor:'#2a2d3e'}},
              timeScale:{{borderColor:'#2a2d3e',timeVisible:false}},
            }});
            const vs = vc.addHistogramSeries({{priceFormat:{{type:'volume'}},priceScaleId:''}});
            vs.priceScale().applyOptions({{scaleMargins:{{top:0.1,bottom:0}}}});
            vs.setData(data.volume); vc.timeScale().fitContent();
            chart.timeScale().subscribeVisibleLogicalRangeChange(r=>vc.timeScale().setVisibleLogicalRange(r));
            vc.timeScale().subscribeVisibleLogicalRangeChange(r=>chart.timeScale().setVisibleLogicalRange(r));
          }})
          .catch(e => {{ document.getElementById('smeta-'+ticker).textContent='Failed: '+e; }});
      }});
    }});

    // ── Sorting ──────────────────────────────────────────────────────────────
    function semiSort(th) {{
      const tbody = document.getElementById('semi-tbody');
      const idx   = th.cellIndex;
      const asc   = th.classList.contains('sort-desc');
      th.closest('thead').querySelectorAll('th').forEach(h => h.classList.remove('sort-asc','sort-desc'));
      th.classList.add(asc ? 'sort-asc' : 'sort-desc');
      const rows = Array.from(tbody.querySelectorAll('.semi-row'));
      rows.sort((a,b) => {{
        const av=a.cells[idx].textContent.trim(), bv=b.cells[idx].textContent.trim();
        const an=parseFloat(av.replace(/[^0-9.-]/g,'')), bn=parseFloat(bv.replace(/[^0-9.-]/g,''));
        const cmp=isNaN(an) ? av.localeCompare(bv) : an-bn;
        return asc ? cmp : -cmp;
      }});
      rows.forEach(r => tbody.appendChild(r));
    }}

    // ── Copy TradingView list ─────────────────────────────────────────────────
    function semiCopy() {{
      const ta  = document.getElementById('semi-tv-list');
      const btn = document.getElementById('semi-copy-btn');
      ta.select(); ta.setSelectionRange(0,99999);
      navigator.clipboard.writeText(ta.value).then(() => {{
        btn.textContent='Copied!'; btn.style.background='#14532d';
        btn.style.borderColor='#22c55e'; btn.style.color='#4ade80';
        setTimeout(()=>{{
          btn.textContent='Copy'; btn.style.background='#1e3a5f';
          btn.style.borderColor='#3b82f6'; btn.style.color='#60a5fa';
        }},2000);
      }});
    }}
    </script>"""

    return page_wrap('Semiconductors', 'semiconductors', content)


# ─── EFI Scanner ──────────────────────────────────────────────────────────────

def _run_efi_scan_job():
    global _job_running, _job_name
    def log(msg):
        with open(LOG_FILE, 'a') as f:
            f.write(msg)
    with open(LOG_FILE, 'w') as f:
        f.write(f"=== EFI Scan ===\nStarted: {datetime.now()}\n\n")
    try:
        run_efi_scan(log_callback=log)
    except Exception as e:
        with open(LOG_FILE, 'a') as f:
            f.write(f"\nFATAL ERROR: {e}\n")
    finally:
        _job_running = False
        _job_name    = None


def start_efi_scan():
    global _job_running, _job_name
    if _job_running:
        return
    _job_running = True
    _job_name    = 'EFI Scan'
    import threading
    threading.Thread(target=_run_efi_scan_job, daemon=True).start()


@app.route('/efi')
def efi_page():
    running = _job_running and _job_name == 'EFI Scan'
    data    = load_last_efi_results()

    fi_color_map = {
        'maroon': ('#7f1d1d', '#fca5a5'),
        'orange': ('#78350f', '#fcd34d'),
        'lime':   ('#14532d', '#86efac'),
        'teal':   ('#134e4a', '#5eead4'),
    }

    table = ''
    if data and data.get('results'):
        rows = ''
        for r in data['results']:
            color, tc = fi_color_map.get(r['fi_color'], ('#1e2130', '#888'))
            rows += f"""<tr style="border-bottom:1px solid #151820">
              <td style="padding:9px 14px;font-weight:700">{r['ticker']}</td>
              <td style="padding:9px 10px;color:#aaa">${r['price']:,.2f}</td>
              <td style="padding:9px 10px;color:#22c55e">{r['norm_price']:+.4f}</td>
              <td style="padding:9px 10px;color:#f87171">{r['histogram']:+.4f}</td>
              <td style="padding:9px 10px;background:{color};color:{tc};text-align:center;font-size:.78rem;font-weight:700">{r['fi_color']}</td>
            </tr>"""
        scan_date = data.get('scan_date', '')
        table = f"""
        <p style="color:#555;font-size:.8rem;margin-bottom:10px">Last scan: {scan_date} — {data['total']} setups</p>
        <div class="card" style="padding:0;overflow:hidden">
          <table style="width:100%;border-collapse:collapse;font-size:.84rem">
            <thead>
              <tr style="border-bottom:2px solid #2a2d3e">
                <th style="text-align:left;padding:9px 14px;color:#555;font-weight:500">Ticker</th>
                <th style="text-align:left;padding:9px 10px;color:#555;font-weight:500">Price</th>
                <th style="text-align:left;padding:9px 10px;color:#555;font-weight:500">Norm Price</th>
                <th style="text-align:left;padding:9px 10px;color:#555;font-weight:500">Histogram</th>
                <th style="text-align:center;padding:9px 10px;color:#555;font-weight:500">FI Color</th>
              </tr>
            </thead>
            <tbody>{rows}</tbody>
          </table>
        </div>"""

    if running:
        log_content = ''
        try:
            with open(LOG_FILE) as f:
                log_content = f.read()
        except Exception:
            pass
        run_btn = '<span class="btn" style="background:#1e2130;color:#555;cursor:not-allowed">⏳ Scanning...</span>'
        matrix_log = f'<pre style="background:#0a0c12;color:#00ff41;padding:16px;border-radius:8px;font-size:.72rem;max-height:300px;overflow-y:auto;margin-top:16px;font-family:monospace">{log_content}</pre>'
    else:
        run_btn    = '<a href="/run-efi" class="btn btn-blue">▶ Run EFI Scan</a>' if is_admin() else ''
        matrix_log = ''

    content = f"""
    <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:20px">
      <div>
        <h2 style="margin:0">EFI Scanner</h2>
        <p style="color:#666;font-size:.83rem;margin:4px 0 0">
          Channel printing + Normalized price &gt; 0 + Histogram &lt; 0 — pullback in trend setup
        </p>
      </div>
      {run_btn}
    </div>
    {matrix_log}
    {table if table else '<p class="note">No scan run yet. Click Run EFI Scan above.</p>'}
    """
    return page_wrap('EFI Scan', 'efi', content, auto_refresh=running)


@app.route('/run-efi')
def run_efi_route():
    if not is_admin():
        return redirect('/efi')
    start_efi_scan()
    return redirect('/efi')


# ─── Indexes & ETFs ───────────────────────────────────────────────────────────

@app.route('/indexes')
def indexes_page():
    # ── Performance heatmap data from DB ──────────────────────────────────────
    all_tickers = ([t for t, _ in SECTOR_ETFS] + [t for t, _ in INDEX_ETFS]
                   + [t for t, _ in MACRO_INSTRUMENTS])
    perf = get_perf_data(all_tickers)

    def heatmap_row(ticker, name, p):
        cells = ''
        for key in ('d1', 'w1', 'm1', 'm3'):
            v   = p[key]
            bg  = perf_color(v)
            tc  = perf_text_color(v)
            txt = f'{("+" if v and v>=0 else "")}{v:.2f}%' if v is not None else '—'
            cells += (f'<td style="background:{bg};color:{tc};text-align:center;'
                      f'padding:9px 6px;font-size:.82rem;font-weight:600;'
                      f'border-right:1px solid #0f1117">{txt}</td>')
        return (f'<tr style="border-bottom:1px solid #0f1117">'
                f'<td style="padding:9px 12px;font-weight:600;white-space:nowrap">{ticker}</td>'
                f'<td style="padding:9px 12px;color:#888;font-size:.8rem;white-space:nowrap">{name}</td>'
                f'{cells}</tr>')

    sector_rows = ''.join(heatmap_row(t, n, perf[t]) for t, n in SECTOR_ETFS)
    index_rows  = ''.join(heatmap_row(t, n, perf[t]) for t, n in INDEX_ETFS)
    macro_rows  = ''.join(heatmap_row(t, n, perf[t]) for t, n in MACRO_INSTRUMENTS)

    debug_bar = ''
    if perf.get('_error'):
        debug_bar = f'<div style="background:#7f1d1d;color:#fca5a5;padding:10px 16px;border-radius:6px;margin-bottom:16px;font-size:.83rem">DB Error: {perf["_error"]}</div>'
    elif perf['_rows_found'] == 0:
        debug_bar = '<div style="background:#78350f;color:#fcd34d;padding:10px 16px;border-radius:6px;margin-bottom:16px;font-size:.83rem">No data found in DB for these tickers — run db_daily_update.py to populate.</div>'

    heatmap_table = lambda rows: f"""
        <table style="width:100%;border-collapse:collapse;font-size:.83rem">
          <thead>
            <tr style="border-bottom:2px solid #2a2d3e">
              <th style="text-align:left;padding:8px 12px;color:#555;font-weight:500;width:70px">Ticker</th>
              <th style="text-align:left;padding:8px 12px;color:#555;font-weight:500">Sector / Name</th>
              <th style="text-align:center;padding:8px 10px;color:#555;font-weight:500;width:80px">1 Day</th>
              <th style="text-align:center;padding:8px 10px;color:#555;font-weight:500;width:80px">1 Week</th>
              <th style="text-align:center;padding:8px 10px;color:#555;font-weight:500;width:80px">1 Month</th>
              <th style="text-align:center;padding:8px 10px;color:#555;font-weight:500;width:80px">3 Month</th>
            </tr>
          </thead>
          <tbody>{rows}</tbody>
        </table>"""

    content = f"""
    <style>
      .ix-section {{ margin-bottom: 32px; }}
      .ix-section h2 {{ font-size: .78rem; font-weight: 600; color: #777;
                       text-transform: uppercase; letter-spacing: .06em; margin-bottom: 14px; }}
    </style>

    {debug_bar}

    <div class="ix-section">
      <h2>Dollar, Commodities &amp; Rates</h2>
      <div style="background:#1a1d2e;border:1px solid #2a2d3e;border-radius:8px;overflow:hidden">
        {heatmap_table(macro_rows)}
      </div>
    </div>

    <div class="ix-section">
      <h2>Sector ETF Performance</h2>
      <div style="background:#1a1d2e;border:1px solid #2a2d3e;border-radius:8px;overflow:hidden">
        {heatmap_table(sector_rows)}
      </div>
    </div>

    <div class="ix-section">
      <h2>Index &amp; Thematic ETF Performance</h2>
      <div style="background:#1a1d2e;border:1px solid #2a2d3e;border-radius:8px;overflow:hidden">
        {heatmap_table(index_rows)}
      </div>
    </div>
    """
    return page_wrap('Indexes & ETFs', 'indexes', content)


def us_index_page(title, active_key, tickers, etf_ticker=''):
    """Generic page builder for US index tabs (Dow/Nasdaq/S&P/Russell)."""
    sparklines = get_us_sparklines_batch(tickers)
    latest     = get_us_latest_prices(tickers)
    with_data  = get_us_tickers_with_data(tickers)

    # ── Breadth calculation from sparklines ──────────────────────────────────
    def breadth(n):
        up = down = flat = no_data = 0
        for t in tickers:
            c = sparklines.get(t, [])
            if len(c) > n:
                if   c[-1] > c[-1-n]: up   += 1
                elif c[-1] < c[-1-n]: down += 1
                else:                 flat += 1
            else:
                no_data += 1
        total = up + down + flat
        up_pct   = round(up   / total * 100, 1) if total else 0
        down_pct = round(down / total * 100, 1) if total else 0
        flat_pct = round(100 - up_pct - down_pct, 1)
        return up, down, flat, up_pct, down_pct, flat_pct, total

    d_up,  d_dn,  d_fl,  d_up_pct,  d_dn_pct,  d_fl_pct,  d_tot  = breadth(1)
    w_up,  w_dn,  w_fl,  w_up_pct,  w_dn_pct,  w_fl_pct,  w_tot  = breadth(5)
    m_up,  m_dn,  m_fl,  m_up_pct,  m_dn_pct,  m_fl_pct,  m_tot  = breadth(21)

    rows_html = ''
    for ticker in tickers:
        closes  = sparklines.get(ticker, [])
        price   = latest.get(ticker)
        svg     = sparkline_svg(closes) if ticker in with_data else ''
        price_s = f'${price:,.2f}' if price else '—'
        day_chg = ''
        if len(closes) >= 2:
            pct = (closes[-1] - closes[-2]) / closes[-2] * 100
            col = '#22c55e' if pct >= 0 else '#ef4444'
            day_chg = f'<span style="color:{col};font-size:.78rem">{"+" if pct>=0 else ""}{pct:.2f}%</span>'
        rows_html += f"""
        <tr class="ux-row" data-ticker="{ticker}" style="cursor:{'pointer' if ticker in with_data else 'default'}">
          <td>
            <div style="display:flex;align-items:center;gap:12px">
              <strong style="color:#60a5fa;min-width:68px;font-size:1rem">{ticker}</strong>
              {svg}
            </div>
          </td>
          <td style="font-weight:700;color:#fff;font-size:1rem">{price_s}</td>
          <td style="font-size:.95rem;font-weight:600">{day_chg}</td>
        </tr>"""

    chart_js = """
    <script>
    document.querySelectorAll('.ux-row').forEach(row => {
      row.addEventListener('click', () => {
        const ticker = row.dataset.ticker;
        const existId = 'udrop-' + ticker;
        const exist = document.getElementById(existId);
        if (exist) { exist.remove(); row.classList.remove('active'); return; }
        document.querySelectorAll('.ux-drop').forEach(d => d.remove());
        document.querySelectorAll('.ux-row.active').forEach(r => r.classList.remove('active'));
        row.classList.add('active');
        const drop = document.createElement('tr');
        drop.id = existId; drop.className = 'ux-drop';
        drop.innerHTML = `<td colspan="3" style="background:#080a10;padding:16px 20px">
          <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:10px">
            <span style="color:#fff;font-weight:700;font-size:1rem">${ticker} <span style="color:#555;font-size:.78rem">NYSE/NASDAQ</span></span>
            <span style="color:#555;font-size:.75rem" id="us-${ticker}">Loading...</span>
          </div>
          <div id="um-${ticker}" style="height:340px;background:#0a0c14;border-radius:6px"></div>
          <div id="uv-${ticker}" style="height:65px;background:#0a0c14;border-radius:6px;margin-top:3px"></div>
        </td>`;
        row.parentNode.insertBefore(drop, row.nextSibling);
        fetch('/api/us-chart/' + ticker)
          .then(r => r.json())
          .then(data => {
            if (data.error) { document.getElementById('us-' + ticker).textContent = data.error; return; }
            document.getElementById('us-' + ticker).textContent = data.bars + ' bars · ' + data.date_range;
            const chart = LightweightCharts.createChart(document.getElementById('um-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: true },
              crosshair: { mode: LightweightCharts.CrosshairMode.Normal },
            });
            const candles = chart.addCandlestickSeries({
              upColor: '#22c55e', downColor: '#ef4444',
              borderUpColor: '#22c55e', borderDownColor: '#ef4444',
              wickUpColor: '#22c55e', wickDownColor: '#ef4444',
            });
            candles.setData(data.ohlcv);
            const ema5  = chart.addLineSeries({ color: '#60a5fa', lineWidth: 1, title: 'EMA5' });
            const ema26 = chart.addLineSeries({ color: '#f59e0b', lineWidth: 1, title: 'EMA26' });
            ema5.setData(data.ema5); ema26.setData(data.ema26);
            const barCount = data.ohlcv.length;
            chart.timeScale().setVisibleLogicalRange({ from: 0, to: barCount + Math.round(barCount * 0.9) });
            chart.priceScale('right').applyOptions({ scaleMargins: { top: 0.12, bottom: 0.18 } });
            const vc = LightweightCharts.createChart(document.getElementById('uv-' + ticker), {
              layout: { background: { color: '#0a0c14' }, textColor: '#888' },
              grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
              rightPriceScale: { borderColor: '#2a2d3e' },
              timeScale: { borderColor: '#2a2d3e', timeVisible: false },
            });
            const vs = vc.addHistogramSeries({ priceFormat: { type: 'volume' }, priceScaleId: '' });
            vs.priceScale().applyOptions({ scaleMargins: { top: 0.1, bottom: 0 } });
            vs.setData(data.volume); vc.timeScale().fitContent();
            chart.timeScale().subscribeVisibleLogicalRangeChange(r => vc.timeScale().setVisibleLogicalRange(r));
            vc.timeScale().subscribeVisibleLogicalRangeChange(r => chart.timeScale().setVisibleLogicalRange(r));
          })
          .catch(e => { document.getElementById('us-' + ticker).textContent = 'Failed: ' + e; });
      });
    });
    </script>"""

    # ── Build donut cards HTML ────────────────────────────────────────────────
    donut_html = ''
    for period, up_pct, dn_pct, fl_pct, up, dn in [
        ('Day',   d_up_pct, d_dn_pct, d_fl_pct, d_up, d_dn),
        ('Week',  w_up_pct, w_dn_pct, w_fl_pct, w_up, w_dn),
        ('Month', m_up_pct, m_dn_pct, m_fl_pct, m_up, m_dn),
    ]:
        pid = period.lower()
        center_style = 'position:absolute;top:50%;left:50%;transform:translate(-50%,-50%);font-size:1.6rem;font-weight:800;color:#fff;white-space:nowrap'
        donut_html += (
            f'<div style="text-align:center">'
            f'<div style="font-size:.82rem;color:#aaa;font-weight:600;text-transform:uppercase;letter-spacing:.08em;margin-bottom:10px">{period}</div>'
            f'<div style="position:relative;width:150px;height:150px">'
            f'<canvas id="donut-{pid}" width="150" height="150"></canvas>'
            f'<div style="{center_style}">{up_pct}%</div>'
            f'</div>'
            f'<div style="font-size:.88rem;margin-top:10px;font-weight:600">'
            f'<span style="color:#22c55e">&#9650; {up} up</span>'
            f'<span style="color:#555;margin:0 8px">/</span>'
            f'<span style="color:#ef4444">&#9660; {dn} down</span>'
            f'</div></div>'
        )

    etf_section = ''
    if etf_ticker:
        etf_section = f"""
        <div id="etf-chart-wrap">
          <div style="font-size:.78rem;color:#888;margin-bottom:8px;font-weight:600">
            {etf_ticker} &nbsp;<span style="color:#555;font-weight:400">— 60 Day</span>
          </div>
          <div id="etf-area" style="height:220px;background:#0a0c14;border-radius:8px"></div>
        </div>
        <script>
        (function(){{
          fetch('/api/us-chart/{etf_ticker}')
            .then(r=>r.json())
            .then(data=>{{
              if(data.error||!data.ohlcv) return;
              const recent = data.ohlcv.slice(-60);
              const LWC = LightweightCharts;
              const chart = LWC.createChart(document.getElementById('etf-area'),{{
                layout:{{background:{{color:'#0a0c14'}},textColor:'#555'}},
                grid:{{vertLines:{{color:'#12141e'}},horzLines:{{color:'#12141e'}}}},
                rightPriceScale:{{borderColor:'#1a1d2e'}},
                timeScale:{{borderColor:'#1a1d2e',timeVisible:false}},
                crosshair:{{mode:LightweightCharts.CrosshairMode.Normal}},
                handleScroll:false, handleScale:false,
              }});
              const area = chart.addAreaSeries({{
                lineColor:'#3b82f6', topColor:'#3b82f644',
                bottomColor:'#3b82f600', lineWidth:2,
              }});
              area.setData(recent.map(b=>({{time:b.time,value:b.close}})));
              chart.timeScale().fitContent();
            }}).catch(()=>{{}});
        }})();
        </script>"""

    content = f"""
    <script src="https://cdn.jsdelivr.net/npm/chart.js@4.4.0/dist/chart.umd.min.js"></script>
    <script src="https://unpkg.com/lightweight-charts@4.1.3/dist/lightweight-charts.standalone.production.js"></script>

    <!-- Dashboard header -->
    <section style="margin-bottom:20px">

      {etf_section}

      <!-- Breadth donuts -->
      <div style="margin-top:18px">
        <p style="font-size:.88rem;color:#888;margin-bottom:14px">
          Percentage of <strong style="color:#fff">{title}</strong> stocks moving up or down over each time period
        </p>
        <div style="display:flex;gap:28px;align-items:flex-start;flex-wrap:wrap">
          {donut_html}
        </div>
      </div>

      <div style="margin-top:14px;font-size:.8rem;color:#444">
        {len(with_data)} of {len(tickers)} tickers with data &nbsp;·&nbsp; click any row to expand chart
      </div>
    </section>

    <script>
    (function(){{
      const donuts = [
        {{ id:'donut-day',   up:{d_up_pct}, dn:{d_dn_pct}, fl:{d_fl_pct} }},
        {{ id:'donut-week',  up:{w_up_pct}, dn:{w_dn_pct}, fl:{w_fl_pct} }},
        {{ id:'donut-month', up:{m_up_pct}, dn:{m_dn_pct}, fl:{m_fl_pct} }},
      ];
      donuts.forEach(d => {{
        const ctx = document.getElementById(d.id).getContext('2d');
        new Chart(ctx, {{
          type: 'doughnut',
          data: {{
            datasets: [{{
              data: [d.up, d.dn, d.fl],
              backgroundColor: ['#22c55e','#ef4444','#1f2235'],
              borderWidth: 0,
              hoverOffset: 4,
            }}]
          }},
          options: {{
            cutout: '70%',
            animation: {{ animateRotate: true, duration: 1200, easing: 'easeInOutQuart' }},
            plugins: {{
              legend: {{ display: false }},
              tooltip: {{
                callbacks: {{
                  label: ctx => ['Up','Down','Flat'][ctx.dataIndex] + ': ' + ctx.parsed + '%'
                }}
              }}
            }}
          }}
        }});
      }});
    }})();
    </script>
    <section>
      <style>
        .ux-table {{ width:100%; border-collapse:collapse; font-size:.95rem; }}
        .ux-table th {{ text-align:left; padding:10px 14px; color:#777;
                       border-bottom:1px solid #2a2d3e; font-weight:500; cursor:pointer; user-select:none; font-size:.82rem; }}
        .ux-table th:hover {{ color:#aaa; }}
        .ux-table th.sort-asc::after  {{ content:' ▲'; font-size:.65rem; color:#60a5fa; }}
        .ux-table th.sort-desc::after {{ content:' ▼'; font-size:.65rem; color:#60a5fa; }}
        .ux-table td {{ padding:10px 14px; border-bottom:1px solid #151820; vertical-align:middle; }}
        .ux-table .ux-row:hover td {{ background:#1f2235; }}
        .ux-table .ux-row.active td {{ background:#1a2235; }}
        .ux-drop td {{ padding:0 !important; }}
      </style>
      <table class="ux-table">
        <thead><tr>
          <th onclick="sortUx(this)">Ticker</th>
          <th onclick="sortUx(this)">Price (USD)</th>
          <th onclick="sortUx(this)">Day %</th>
        </tr></thead>
        <tbody id="ux-tbody">{rows_html}</tbody>
      </table>
    </section>
    <script>
    function sortUx(th) {{
      const tbody = document.getElementById('ux-tbody');
      const idx = th.cellIndex;
      const asc = th.classList.contains('sort-desc');
      th.closest('thead').querySelectorAll('th').forEach(h => h.classList.remove('sort-asc','sort-desc'));
      th.classList.add(asc ? 'sort-asc' : 'sort-desc');
      const rows = Array.from(tbody.querySelectorAll('.ux-row'));
      rows.sort((a, b) => {{
        const av = a.cells[idx].textContent.trim();
        const bv = b.cells[idx].textContent.trim();
        const an = parseFloat(av.replace('$','').replace(',','')), bn = parseFloat(bv.replace('$','').replace(',',''));
        const cmp = isNaN(an) ? av.localeCompare(bv) : an - bn;
        return asc ? cmp : -cmp;
      }});
      rows.forEach(r => tbody.appendChild(r));
    }}
    </script>
    {chart_js}"""

    return page_wrap(title, active_key, content)


@app.route('/dow')
def dow_page():
    return us_index_page('Dow Jones 30', 'dow', DOW_30, etf_ticker='DIA')


@app.route('/nasdaq')
def nasdaq_page():
    return us_index_page('Nasdaq 100', 'nasdaq', NASDAQ_100, etf_ticker='QQQ')


@app.route('/sp500')
def sp500_page():
    return us_index_page('S&P 500', 'sp500', SP500_TICKERS, etf_ticker='SPY')


@app.route('/russell')
def russell_page():
    known = set(DOW_30) | set(NASDAQ_100) | set(SP500_TICKERS)
    all_us = get_us_all_tickers_with_data()
    russell_tickers = sorted(t for t in all_us if t not in known)
    return us_index_page('Russell / Small Caps', 'russell', russell_tickers, etf_ticker='IWM')


# ─── Options 101 Demo (Black-Scholes) ──────────────────────────────────────────
# Educational-only: dummy options chains + simulated 2-week call trades on a
# spread of real, currently-cheap ($1-$100) stocks, priced with textbook
# Black-Scholes over real closing prices. Not real options market data —
# there's no options feed in this app.

OPTIONS_DEMO_R             = 0.045   # assumed risk-free rate
OPTIONS_DEMO_HOLD_DAYS     = 10      # ~2 trading weeks
OPTIONS_DEMO_DTE_AT_ENTRY  = 45      # calendar days to expiration when the trade opens
CHEAP_PRICE_LOW            = 1.0
CHEAP_PRICE_HIGH           = 100.0
CHEAP_MIN_BARS             = 60      # enough history for the chart + 2-week walkthrough
CHEAP_REFERENCE_COUNT      = 10


def get_cheap_stock_rows(conn):
    """Tickers currently priced $1-$100 with enough history for the demo, cheapest first."""
    with conn.cursor() as cur:
        cur.execute("""
            SELECT p.ticker, p.close, cnt.n
            FROM prices p
            INNER JOIN (SELECT ticker, MAX(date) AS max_date FROM prices GROUP BY ticker) latest
              ON p.ticker = latest.ticker AND p.date = latest.max_date
            INNER JOIN (SELECT ticker, COUNT(*) AS n FROM prices GROUP BY ticker) cnt
              ON cnt.ticker = p.ticker
            WHERE p.close BETWEEN %s AND %s AND cnt.n >= %s
            ORDER BY p.close ASC
        """, (CHEAP_PRICE_LOW, CHEAP_PRICE_HIGH, CHEAP_MIN_BARS))
        return cur.fetchall()  # [(ticker, close, n), ...]


def pick_price_spread(rows, n):
    """Pick n rows evenly spaced across the (price-sorted) list, not just the first n."""
    if len(rows) <= n:
        return list(rows)
    picked, seen = [], set()
    step = len(rows) / float(n)
    for i in range(n):
        idx = min(int(i * step), len(rows) - 1)
        while idx in seen and idx < len(rows) - 1:
            idx += 1
        seen.add(idx)
        picked.append(rows[idx])
    return picked


def build_options_demo_for_ticker(conn, ticker):
    df = get_ticker_data(conn, ticker)
    if df is None or len(df) < OPTIONS_DEMO_HOLD_DAYS + 15:
        return None

    chart_df = df.tail(40)
    walk_df  = df.tail(OPTIONS_DEMO_HOLD_DAYS)

    entry_ts    = walk_df.index[0]
    exit_ts     = walk_df.index[-1]
    entry_spot  = float(walk_df.iloc[0]['close'])
    iv          = assumed_iv_for_price(entry_spot)
    increment   = strike_increment_for_price(entry_spot)
    expiry_date = entry_ts + pd.Timedelta(days=OPTIONS_DEMO_DTE_AT_ENTRY)
    strike      = max(round(entry_spot / increment) * increment, increment)

    entry_greeks = bs_price_greeks(entry_spot, strike, OPTIONS_DEMO_DTE_AT_ENTRY / 365.0,
                                    effective_iv(iv, entry_spot, strike), OPTIONS_DEMO_R, 'call')
    entry_premium = entry_greeks['price']

    def to_time(ts):
        return ts.strftime('%Y-%m-%d')

    ohlcv = [
        {'time': to_time(ts), 'open': float(r['open']), 'high': float(r['high']),
         'low': float(r['low']), 'close': float(r['close'])}
        for ts, r in chart_df.iterrows()
    ]

    # Static chain snapshot at entry date — 9 strikes around ATM
    chain = []
    for offset in range(-4, 5):
        k = max(strike + offset * increment, increment)
        k_iv = effective_iv(iv, entry_spot, k)
        c = bs_price_greeks(entry_spot, k, OPTIONS_DEMO_DTE_AT_ENTRY / 365.0, k_iv, OPTIONS_DEMO_R, 'call')
        p = bs_price_greeks(entry_spot, k, OPTIONS_DEMO_DTE_AT_ENTRY / 365.0, k_iv, OPTIONS_DEMO_R, 'put')
        chain.append({
            'strike': round(k, 2),
            'call_price': round(c['price'], 2), 'call_delta': round(c['delta'], 3),
            'put_price': round(p['price'], 2), 'put_delta': round(p['delta'], 3),
            'is_strike': abs(k - strike) < 0.01,
        })

    # Day-by-day walkthrough over the 2-week hold, real closes + decaying real DTE
    walkthrough = []
    for ts, row in walk_df.iterrows():
        spot = float(row['close'])
        dte_days = max((expiry_date - ts).days, 0)
        g = bs_price_greeks(spot, strike, dte_days / 365.0, effective_iv(iv, spot, strike), OPTIONS_DEMO_R, 'call')
        intrinsic = max(spot - strike, 0.0)
        extrinsic = g['price'] - intrinsic
        pnl = (g['price'] - entry_premium) * 100.0
        pnl_pct = (g['price'] / entry_premium - 1.0) * 100.0 if entry_premium else 0.0
        walkthrough.append({
            'date': to_time(ts), 'spot': round(spot, 2), 'dte': dte_days,
            'price': round(g['price'], 2), 'delta': round(g['delta'], 3), 'theta': round(g['theta'], 3),
            'intrinsic': round(intrinsic, 2), 'extrinsic': round(extrinsic, 2),
            'pnl': round(pnl, 2), 'pnl_pct': round(pnl_pct, 1),
        })

    return {
        'ticker': ticker,
        'entry_date': to_time(entry_ts), 'exit_date': to_time(exit_ts),
        'expiry_date': expiry_date.strftime('%Y-%m-%d'),
        'strike': round(strike, 2), 'iv': iv, 'r': OPTIONS_DEMO_R,
        'entry_spot': round(entry_spot, 2), 'entry_premium': round(entry_premium, 2),
        'contract_cost': round(entry_premium * 100.0, 2),
        'ohlcv': ohlcv, 'chain': chain, 'walkthrough': walkthrough,
    }


@app.route('/api/options-demo')
def api_options_demo():
    try:
        conn = get_connection()
        rows = get_cheap_stock_rows(conn)
        if not rows:
            conn.close()
            return jsonify({'error': f'No tickers found priced between ${CHEAP_PRICE_LOW:.0f}-${CHEAP_PRICE_HIGH:.0f}.'})

        reference = pick_price_spread(rows, CHEAP_REFERENCE_COUNT)

        reference_out = []
        for ticker, close, n in reference:
            close = float(close)
            iv  = assumed_iv_for_price(close)
            inc = strike_increment_for_price(close)
            k   = max(round(close / inc) * inc, inc)
            g   = bs_price_greeks(close, k, 30 / 365.0, iv, OPTIONS_DEMO_R, 'call')
            reference_out.append({
                'ticker': ticker, 'price': round(close, 2), 'iv': iv,
                'strike': round(k, 2), 'atm_call_premium': round(g['price'], 2),
            })

        # Deep-dive walkthroughs: cheapest, middle, and priciest of the spread
        pick_idxs = sorted(set([0, len(reference) // 2, len(reference) - 1]))
        deep_tickers = [reference[i][0] for i in pick_idxs]

        examples = []
        for ticker in deep_tickers:
            demo = build_options_demo_for_ticker(conn, ticker)
            if demo:
                examples.append(demo)

        conn.close()

        if not examples:
            return jsonify({'error': 'Could not build any example trades from the current price data.'})

        return jsonify({'examples': examples, 'reference': reference_out})
    except Exception as e:
        return jsonify({'error': str(e)})


# ─── Kids Corner ────────────────────────────────────────────────────────────────
# Candle-pattern learning page: a pattern description + 2-3 real historical
# examples per pattern, pulled straight from the existing scanners' saved
# results (no separate content pipeline needed). Patterns without a scanner
# yet (Double Top, Tweezers, High-Low Levels) show a "coming soon" placeholder
# until real detection logic exists for them.

KIDS_PATTERNS = [
    {
        'key': 'hammer', 'emoji': '🔨', 'name': 'Hammer',
        'blurb': "A little candle with a long tail hanging below it. Sellers pushed the price down during the day, but buyers stepped in and pushed it back up before the day ended.",
        'lookfor': "Look for: a small body near the TOP of the candle, with a long wick underneath — at least twice as long as the body.",
        'loader': 'hammer',
    },
    {
        'key': 'marubozu', 'emoji': '🟩', 'name': 'Marubozu',
        'blurb': "A big solid candle with barely any wicks at all. It means buyers were in control the whole day, from open to close, with barely a fight.",
        'lookfor': "Look for: a big body that fills almost the whole candle, with tiny or no wicks on either end.",
        'loader': 'marubozu',
    },
    {
        'key': 'double_top', 'emoji': '⛰️', 'name': 'Double Top',
        'blurb': "Price climbs up, comes back down, then climbs up again to about the same height — like two mountain peaks side by side. It can mean the price is struggling to break higher.",
        'lookfor': None, 'loader': None,
    },
    {
        'key': 'tweezers', 'emoji': '🥢', 'name': 'Tweezers',
        'blurb': "Two candles in a row with almost the exact same high point (or the same low point) — like a pair of tweezers pinching the price at one level.",
        'lookfor': None, 'loader': None,
    },
    {
        'key': 'high_low_levels', 'emoji': '📏', 'name': 'High-Low Levels',
        'blurb': "Prices often bounce off the same 'ceiling' or 'floor' again and again. Spotting those levels helps you guess what might happen when price gets there next time.",
        'lookfor': None, 'loader': None,
    },
]


def _kids_pattern_examples(loader_key, limit=3):
    loaders = {'hammer': load_last_hammer_results, 'marubozu': load_last_marubozu_results}
    date_keys = {'hammer': 'hammer_date', 'marubozu': 'marubozu_date'}
    loader = loaders.get(loader_key)
    if not loader:
        return []
    data = loader()
    if not data or not data.get('results'):
        return []
    dk = date_keys[loader_key]
    results = sorted(data['results'], key=lambda r: r['score'], reverse=True)
    seen, examples = set(), []
    for r in results:
        if r['ticker'] in seen:
            continue  # one example per ticker — more variety for kids to see
        seen.add(r['ticker'])
        examples.append({'ticker': r['ticker'], 'date': r[dk], 'score': r['score']})
        if len(examples) >= limit:
            break
    return examples


@app.route('/kids')
def kids_page():
    cards_html = ''
    for p in KIDS_PATTERNS:
        examples = _kids_pattern_examples(p['loader']) if p['loader'] else []

        lookfor_html = f'<p style="color:#93c5fd;font-size:.85rem;margin-bottom:14px">{p["lookfor"]}</p>' if p['lookfor'] else ''

        if p['loader'] and examples:
            ex_buttons = ''
            ex_panels = ''
            for i, ex in enumerate(examples):
                cid = f"{p['key']}-{i}"
                ex_buttons += f"""<button class="kids-ex-btn" onclick="showKidsExample(event, '{cid}')">{ex['ticker']}</button>"""
                ex_panels += f"""
                <div id="kids-panel-{cid}" class="kids-ex-panel" style="display:none">
                  <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:8px">
                    <span style="font-weight:700;color:#fff">{ex['ticker']} — {ex['date']}</span>
                    <a href="/chart/{ex['ticker']}" style="font-size:.78rem;color:#60a5fa">Open full chart →</a>
                  </div>
                  <div id="kids-chart-{cid}" style="height:280px;background:#0a0c14;border-radius:6px"></div>
                </div>"""
            examples_block = f"""
              <div style="margin-bottom:10px">
                <span style="font-size:.78rem;color:#666;margin-right:8px">Real examples:</span>
                {ex_buttons}
              </div>
              {ex_panels}"""
        elif p['loader']:
            examples_block = '<p class="note">No real examples saved yet — run the scanner to find some!</p>'
        else:
            examples_block = '<p class="note">🚧 Still gathering great examples of this one — check back soon!</p>'

        cards_html += f"""
        <div class="card" style="margin-bottom:16px">
          <div style="display:flex;align-items:center;gap:10px;margin-bottom:8px">
            <span style="font-size:1.6rem">{p['emoji']}</span>
            <span style="font-size:1.15rem;font-weight:700;color:#fff">{p['name']}</span>
          </div>
          <p style="color:#aaa;font-size:.9rem;line-height:1.6;margin-bottom:8px">{p['blurb']}</p>
          {lookfor_html}
          {examples_block}
        </div>"""

    content = f"""
    <style>
      .kids-ex-btn {{ background:#1e3a5f;border:1px solid #3b82f6;color:#93c5fd;padding:5px 14px;
                     border-radius:6px;cursor:pointer;font-size:.8rem;font-weight:600;margin-right:6px }}
      .kids-ex-btn:hover {{ background:#2d4d75 }}
      .kids-ex-btn.active {{ background:#3b82f6;color:#fff }}
      .kids-ex-panel {{ background:#0d0f1a;border:1px solid #1e2235;border-radius:8px;padding:14px;margin-top:8px }}
    </style>

    <div style="text-align:center;margin-bottom:32px;padding:20px 0">
      <h1 style="font-size:2rem;font-weight:800;margin-bottom:12px">🎓 Kids Corner</h1>
      <p style="color:#888;font-size:1rem;max-width:560px;margin:0 auto;line-height:1.7">
        Learn to read stock charts! Every pattern below is something real traders look
        for — click a ticker under any pattern to see it happen on a real stock chart.
      </p>
    </div>

    {cards_html}

    <script src="https://unpkg.com/lightweight-charts@4.1.3/dist/lightweight-charts.standalone.production.js"></script>
    <script>
    class KidsPatternLineRenderer {{
      constructor(time, color, chart) {{ this._time = time; this._color = color; this._chart = chart; }}
      draw(target) {{
        const x = this._chart.timeScale().timeToCoordinate(this._time);
        if (x === null) return;
        target.useBitmapCoordinateSpace(scope => {{
          const ctx = scope.context;
          const xb = Math.round(x * scope.horizontalPixelRatio);
          ctx.save();
          ctx.beginPath();
          ctx.moveTo(xb, 0);
          ctx.lineTo(xb, scope.bitmapSize.height);
          ctx.strokeStyle = this._color;
          ctx.lineWidth = Math.round(2 * scope.horizontalPixelRatio);
          ctx.setLineDash([6, 4]);
          ctx.stroke();
          ctx.restore();
        }});
      }}
    }}
    class KidsPatternLinePaneView {{
      constructor(time, color, chart) {{ this._renderer = new KidsPatternLineRenderer(time, color, chart); }}
      renderer() {{ return this._renderer; }}
      zOrder() {{ return 'normal'; }}
    }}
    class KidsPatternLine {{
      constructor(time, color = '#f59e0b') {{ this._time = time; this._color = color; this._chart = null; this._views = []; }}
      attached({{ chart }}) {{ this._chart = chart; this._views = [new KidsPatternLinePaneView(this._time, this._color, chart)]; }}
      detached() {{ this._views = []; }}
      paneViews() {{ return this._views; }}
      updateAllViews() {{}}
    }}

    const kidsLoadedCharts = new Set();

    function showKidsExample(evt, cid) {{
      const panel = document.getElementById('kids-panel-' + cid);
      const isOpen = panel.style.display !== 'none';
      // Close all panels + reset button states for this pattern's group
      const group = cid.substring(0, cid.lastIndexOf('-'));
      document.querySelectorAll('[id^="kids-panel-' + group + '-"]').forEach(p => p.style.display = 'none');
      document.querySelectorAll('.kids-ex-btn').forEach(b => {{
        if (b.getAttribute('onclick').includes(group + '-')) b.classList.remove('active');
      }});
      if (isOpen) return;

      panel.style.display = 'block';
      evt.target.classList.add('active');

      if (kidsLoadedCharts.has(cid)) return;
      kidsLoadedCharts.add(cid);

      const ticker = document.getElementById('kids-panel-' + cid).querySelector('span').textContent.split(' — ')[0];
      const dateStr = document.getElementById('kids-panel-' + cid).querySelector('span').textContent.split(' — ')[1];

      fetch('/api/us-chart/' + ticker)
        .then(r => r.json())
        .then(data => {{
          if (data.error) {{ document.getElementById('kids-chart-' + cid).textContent = data.error; return; }}
          const chart = LightweightCharts.createChart(document.getElementById('kids-chart-' + cid), {{
            layout: {{ background: {{ color: '#0a0c14' }}, textColor: '#888' }},
            grid: {{ vertLines: {{ color: '#1a1d2e' }}, horzLines: {{ color: '#1a1d2e' }} }},
            rightPriceScale: {{ borderColor: '#2a2d3e' }},
            timeScale: {{ borderColor: '#2a2d3e', timeVisible: true }},
          }});
          const candles = chart.addCandlestickSeries({{
            upColor: '#22c55e', downColor: '#ef4444',
            borderUpColor: '#22c55e', borderDownColor: '#ef4444',
            wickUpColor: '#22c55e', wickDownColor: '#ef4444',
          }});
          candles.setData(data.ohlcv);
          const targetMs = new Date(dateStr).getTime();
          let snapDate = dateStr, minDiff = Infinity;
          for (const bar of data.ohlcv) {{
            const diff = Math.abs(new Date(bar.time).getTime() - targetMs);
            if (diff < minDiff) {{ minDiff = diff; snapDate = bar.time; }}
          }}
          candles.attachPrimitive(new KidsPatternLine(snapDate));
          const barCount = data.ohlcv.length;
          chart.timeScale().setVisibleLogicalRange({{ from: Math.max(0, barCount - 60), to: barCount + 5 }});
        }})
        .catch(e => {{ document.getElementById('kids-chart-' + cid).textContent = 'Failed: ' + e; }});
    }}
    </script>"""

    return page_wrap('Kids Corner', 'kids', content)


# ─── Signals — public results feed ─────────────────────────────────────────────
# Aggregates the current top 2-3 picks from every scanner onto one public page
# (no admin login required) with a plain-English reason built from that row's
# real values. Scores aren't comparable across scanners (Fader's R:R vs
# Marubozu's body% vs EFI's qualitative color), so this is grouped by scanner
# rather than one mixed leaderboard.

def _price_channel_daily_results():
    data = load_last_price_channel_results()
    if not data:
        return None
    return data.get('daily', {}).get('results')


SIGNAL_FEED_SPECS = [
    {
        'key': 'fader', 'label': 'Fader',
        'loader': load_last_fader_results, 'top_n': 3,
        'sort': lambda r: r['rr'],
        'reasoning': lambda r: (
            f"Channel coiled and the fader signal turned bullish — price ${r['price']:.2f} "
            f"sitting at {r['position_pct']:.1f}% of its range, targeting ${r['L75']:.2f} "
            f"with a stop near ${r['L0']:.2f} ({r['rr']:.1f}x reward:risk)."),
    },
    {
        'key': 'hammer', 'label': 'Hammer',
        'loader': load_last_hammer_results, 'top_n': 3,
        'sort': lambda r: r['score'],
        'reasoning': lambda r: (
            f"Hammer on {r['hammer_date']}: wick {r['wick_ratio']}x the body, closed at "
            f"{r['close_pct']}% of the day's range" +
            (", with a volume surge" if r.get('vol_surge') else '') + '.'),
    },
    {
        'key': 'marubozu', 'label': 'Marubozu',
        'loader': load_last_marubozu_results, 'top_n': 3,
        'sort': lambda r: r['score'],
        'reasoning': lambda r: (
            f"Marubozu on {r['marubozu_date']}: {r['body_pct']}% solid body, wicks "
            f"{r['upper_wick_pct']}%/{r['lower_wick_pct']}% — clean momentum candle" +
            (", with a volume surge" if r.get('vol_surge') else '') + '.'),
    },
    {
        'key': 'extreme', 'label': 'Extreme (TD + ADX)',
        'loader': load_last_extreme_results, 'top_n': 3,
        'sort': lambda r: r['score'],
        'reasoning': lambda r: (
            f"{r['direction'].title()} setup on {r['signal_date']} — TD Buy count "
            f"{r['td_buy_count']}, TD Sell count {r['td_sell_count']}" +
            (f", ADX momentum warning {r['adx_signal']:+.1f}" if r.get('adx_signal') is not None else '') + '.'),
    },
    {
        'key': 'gapdown', 'label': 'Gap Down',
        'loader': load_last_gapdown_results, 'top_n': 3,
        'sort': lambda r: r['score'],
        'reasoning': lambda r: (
            f"Gapped down {r['gap_pct']}% on {r['gap_date']}, now {r['fill_pct']}% filled, "
            f"closed at {r['close_pct']}% of the day's range" +
            (", recovered intraday" if r.get('recovered_intraday') else '') + '.'),
    },
    {
        'key': 'wick', 'label': 'Wick',
        'loader': load_last_wick_results, 'top_n': 3,
        'sort': lambda r: r['score'],
        'reasoning': lambda r: (
            f"Long lower wick week of {r['wick_date']}: {r['wick_ratio']}x the body, held "
            f"{r['weeks_held']} weeks, closed at {r['close_pct']}% of the week's range."),
    },
    {
        'key': 'efi', 'label': 'EFI (Elder Force Index)',
        'loader': load_last_efi_results, 'top_n': 3,
        'sort': lambda r: abs(r['histogram']),
        'reasoning': lambda r: (
            f"Force Index turned {r['fi_color']} at ${r['price']:.2f} — normalized price "
            f"{r['norm_price']:+.4f}, histogram {r['histogram']:+.4f}."),
    },
    {
        'key': 'channel', 'label': 'Channel Squeeze',
        'loader': load_last_results, 'top_n': 3,
        'sort': lambda r: r['score'],
        'reasoning': lambda r: (
            "Compressed on both daily & weekly timeframes" if r['score'] == 2
            else "Compressed on the daily timeframe") + " — EMA5/EMA26 squeezed inside ATR.",
    },
    {
        'key': 'price-channel', 'label': 'Price Channel',
        'loader': _price_channel_daily_results, 'top_n': 3, 'raw_results': True,
        'sort': lambda r: r['score'],
        'reasoning': lambda r: (
            f"Ascending channel — price ${r['current']:,.2f} between ${r['lower']:,.2f} support "
            f"and ${r['upper']:,.2f} resistance (R² {r['r2']}), tested {r['low_touches']}x "
            f"low / {r['high_touches']}x high."),
    },
    {
        'key': 'range-oscillator', 'label': 'Range Oscillator Breakout',
        'loader': load_last_range_oscillator_results, 'top_n': 3,
        'sort': lambda r: r['score'],
        'reasoning': lambda r: (
            f"Fresh {r['direction']} breakout on {r['signal_date']}: closed outside its normal "
            f"volatility range (osc {r['osc']:+.1f}), held {r['days_held']} day"
            f"{'s' if r['days_held'] != 1 else ''} since" +
            (", with a volume surge" if r.get('vol_surge') else '') + '.'),
    },
    {
        'key': 'swing', 'label': 'Weekly Swing Low',
        'loader': load_last_swing_results, 'top_n': 3,
        'sort': lambda r: r['score'],
        'reasoning': lambda r: (
            f"Green dot confirming this week — the {r['pivot_date']} low held as the lowest "
            f"weekly low for 10 straight weeks, price now {r['bounce_pct']:+.1f}% off it, "
            f"liquidity zone {'still unfilled' if not r.get('filled') else 'already filled'}" +
            (", with a volume surge" if r.get('vol_surge') else '') + '.'),
    },
    {
        'key': 'higher-low', 'label': 'Weekly Higher Low',
        'loader': load_last_higher_low_results, 'top_n': 3,
        'sort': lambda r: r['score'],
        'reasoning': lambda r: (
            f"Higher-low shape confirmed {r['c_date']}: flushed {r['flush_pct']:.1f}% below the "
            f"{r['a_date']} low, then bounced {r['recover_pct']:.1f}% to print a new low that's "
            f"actually higher" +
            (" — and reclaimed above the prior low entirely" if r.get('reclaimed_a') else '') +
            (", with a volume surge" if r.get('vol_surge') else '') + '.'),
    },
    {
        'key': 'extreme-exit', 'label': 'Weekly Extreme Exit',
        'loader': load_last_extreme_exit_results, 'top_n': 3,
        'sort': lambda r: r['score'],
        'reasoning': lambda r: (
            f"Weekly bearish extreme just stopped confirming — {r['extreme_date']} closed at "
            f"osc {r['osc_at_extreme']:+.1f} outside the normal range, {r['exit_date']} came back "
            f"inside" +
            (f" and is still climbing (osc {r['osc_now']:+.1f})" if r.get('osc_now') is not None else '') +
            (", extreme was sustained 2+ weeks" if r.get('sustained') else '') + '.'),
    },
    {
        'key': 'doublebottom', 'label': 'Gap Down Double Bottom',
        'loader': load_last_doublebottom_results, 'top_n': 3,
        'sort': lambda r: r['score'],
        'reasoning': lambda r: (
            f"Gapped down {r['gap_pct']}% on {r['gap_date']} to ${r['gap_low']:.2f}, matching "
            f"the {r['first_bottom_date']} low ({r['touches']}x confirmed touches) — neckline at "
            f"${r['neckline']:.2f} (+{r['neckline_pct']:.0f}%), price ${r['price']:.2f} sitting at "
            f"{r['position_pct']}% of its range" +
            (", with a volume surge on the gap" if r.get('vol_surge') else '') +
            (", recovered intraday" if r.get('recovered_intraday') else '') + '.'),
    },
]


def _signal_section(spec):
    try:
        loaded = spec['loader']()
    except Exception:
        loaded = None
    results = loaded if spec.get('raw_results') else (loaded or {}).get('results')
    if not results:
        return f'<section><h2>{spec["label"]}</h2><p class="note">No signals yet — check back after the next scan.</p></section>'

    top = sorted(results, key=spec['sort'], reverse=True)[:spec['top_n']]
    cards = ''
    for r in top:
        try:
            reason = spec['reasoning'](r)
        except Exception:
            continue
        cards += f"""
        <div class="card" style="margin-bottom:10px;padding:16px">
          <a href="/chart/{r['ticker']}" style="font-weight:700;font-size:1.05rem">{r['ticker']}</a>
          <p style="color:#aaa;font-size:.85rem;line-height:1.5;margin-top:6px">{reason}</p>
        </div>"""
    if not cards:
        cards = '<p class="note">No signals yet — check back after the next scan.</p>'
    return f'<section><h2>{spec["label"]}</h2>{cards}</section>'


@app.route('/signals')
def signals_page():
    content = f"""
    <div style="margin-bottom:24px">
      <p class="note" style="font-size:.85rem">
        Current top picks across every scanner, refreshed each time a scan runs.
      </p>
    </div>
    {''.join(_signal_section(s) for s in SIGNAL_FEED_SPECS)}
    """
    return page_wrap('Signals', 'signals', content)


# ─── How It Works — Options 101 ────────────────────────────────────────────────

@app.route('/how-it-works')
def how_it_works():
    content = """
    <style>
      .step-grid { display:grid; grid-template-columns:repeat(auto-fill,minmax(240px,1fr)); gap:16px; margin-bottom:28px; }
      .opt-card { background:#13151f;border:1px solid #2a2d3e;border-radius:10px;padding:18px 20px;font-size:.85rem;color:#aaa;line-height:1.6 }
      .opt-card b { color:#e0e0e0 }
      .opt-table { width:100%;border-collapse:collapse;font-size:.82rem;min-width:640px }
      .opt-table th { text-align:center;padding:8px 10px;color:#555;border-bottom:1px solid #2a2d3e;font-weight:500;white-space:nowrap }
      .opt-table td { text-align:center;padding:7px 10px;border-bottom:1px solid #151820;white-space:nowrap }
      .opt-table tr:hover td { background:#1f2235 }
      .opt-table tr.atm-row td { background:#1a2233 }
    </style>

    <!-- Hero -->
    <div style="text-align:center;margin-bottom:36px;padding:20px 0">
      <h1 style="font-size:2rem;font-weight:800;margin-bottom:12px">🎓 Options 101</h1>
      <p style="color:#888;font-size:1rem;max-width:620px;margin:0 auto;line-height:1.7">
        Options aren't part of the Jimmy's Picks system, but a lot of members ask how they work.
        Below are worked examples on real, currently-cheap stocks ($1&ndash;$100) &mdash; a dummy
        options chain and a full day-by-day walkthrough of a 2-week call trade, priced with the
        Black-Scholes model, the same math real options desks use.
      </p>
    </div>

    <!-- Concept cards -->
    <div class="step-grid">
      <div class="opt-card"><b>Call Option</b><br>The right (not the obligation) to BUY 100 shares at a fixed "strike" price, any time before expiration. Buy calls when you expect the stock to go UP.</div>
      <div class="opt-card"><b>Put Option</b><br>The right to SELL 100 shares at a fixed strike. Buy puts when you expect the stock to go DOWN.</div>
      <div class="opt-card"><b>Premium</b><br>What you pay to buy the option, quoted per share. 1 contract = 100 shares, so a $2.50 premium costs $250 total.</div>
      <div class="opt-card"><b>Theta (Time Decay)</b><br>Options lose value every day just from time passing, even if the stock doesn't move. That's the cost of the leverage you're buying.</div>
    </div>

    <div id="options-status" style="color:#555;font-size:.8rem;margin:20px 0">Loading options examples…</div>

    <h2 style="font-size:.8rem;color:#555;text-transform:uppercase;letter-spacing:.1em;margin-bottom:8px">Stocks Trading Between $1 &ndash; $100 Right Now</h2>
    <p style="color:#666;font-size:.8rem;margin-bottom:12px">A spread of 10 real tickers currently priced in that range, with a quick at-the-money call premium for each (Black-Scholes, ~30 days to expiry, tiered assumed IV). The 3 highlighted rows get a full trade walkthrough below.</p>
    <div id="options-reference-table" style="overflow-x:auto;margin-bottom:16px"></div>

    <div id="options-examples"></div>

    <script src="https://unpkg.com/lightweight-charts@4.1.3/dist/lightweight-charts.standalone.production.js"></script>
    <script>
    fetch('/api/options-demo')
      .then(r => r.json())
      .then(data => {
        const statusEl = document.getElementById('options-status');
        if (data.error) { statusEl.textContent = 'Could not load examples: ' + data.error; return; }
        statusEl.style.display = 'none';

        const deepTickers = data.examples.map(e => e.ticker);

        // Reference table of 10 cheap stocks
        let refHtml = '<table class="opt-table"><tr>' +
          '<th>Ticker</th><th>Price</th><th>Assumed IV</th><th>ATM Strike</th><th>~30-Day ATM Call</th></tr>';
        data.reference.forEach(r => {
          const hl = deepTickers.includes(r.ticker);
          refHtml += '<tr class="' + (hl ? 'atm-row' : '') + '">' +
            '<td style="font-weight:700">' + r.ticker + (hl ? ' ↓' : '') + '</td>' +
            '<td>$' + r.price.toFixed(2) + '</td>' +
            '<td style="color:#666">' + (r.iv * 100).toFixed(0) + '%</td>' +
            '<td>$' + r.strike.toFixed(2) + '</td>' +
            '<td style="color:#60a5fa">$' + r.atm_call_premium.toFixed(2) + '</td>' +
            '</tr>';
        });
        refHtml += '</table>';
        document.getElementById('options-reference-table').innerHTML = refHtml;

        // Full walkthrough blocks, one per deep-dive example
        const root = document.getElementById('options-examples');
        root.innerHTML = data.examples.map((ex, i) => `
          <div style="margin-top:48px;padding-top:32px;border-top:1px solid #2a2d3e">
            <h3 style="font-size:1.1rem;font-weight:700;margin-bottom:6px">${ex.ticker} — $${ex.entry_spot.toFixed(2)} stock</h3>
            <div id="ex-summary-${i}" style="font-size:.95rem;color:#e0e0e0;margin-bottom:14px;line-height:1.8"></div>
            <div id="ex-chart-${i}" style="width:100%;height:320px;background:#0a0c14;border-radius:6px;margin-bottom:24px"></div>
            <h4 style="font-size:.75rem;color:#555;text-transform:uppercase;letter-spacing:.08em;margin-bottom:8px">Dummy Options Chain (at entry, ${(ex.iv * 100).toFixed(0)}% assumed IV)</h4>
            <div id="ex-chain-${i}" style="overflow-x:auto;margin-bottom:24px"></div>
            <h4 style="font-size:.75rem;color:#555;text-transform:uppercase;letter-spacing:.08em;margin-bottom:8px">The Trade — Day by Day Over 2 Weeks</h4>
            <div id="ex-walk-${i}" style="overflow-x:auto;margin-bottom:8px"></div>
            <p style="color:#666;font-size:.78rem;margin-bottom:12px">P&amp;L per contract (100 shares). Green = profit, red = loss vs. the entry premium.</p>
            <div id="ex-pnl-${i}" style="width:100%;height:180px;background:#0a0c14;border-radius:6px"></div>
          </div>
        `).join('');

        data.examples.forEach((ex, i) => {
          document.getElementById('ex-summary-' + i).innerHTML =
            'On <strong>' + ex.entry_date + '</strong>, with ' + ex.ticker + ' trading at <strong>$' + ex.entry_spot.toFixed(2) + '</strong>, ' +
            'you buy <strong>1 ' + ex.ticker + ' $' + ex.strike.toFixed(2) + ' Call</strong> expiring ' + ex.expiry_date + ' for ' +
            '<strong>$' + ex.entry_premium.toFixed(2) + '</strong> per share &mdash; ' +
            '<strong style="color:#f59e0b">$' + ex.contract_cost.toFixed(2) + '</strong> total for the contract.';

          // Price chart
          const chart = LightweightCharts.createChart(document.getElementById('ex-chart-' + i), {
            layout: { background: { color: '#0a0c14' }, textColor: '#888' },
            grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
            rightPriceScale: { borderColor: '#2a2d3e' },
            timeScale: { borderColor: '#2a2d3e', timeVisible: true },
            crosshair: { mode: LightweightCharts.CrosshairMode.Normal },
          });
          const candles = chart.addCandlestickSeries({
            upColor: '#22c55e', downColor: '#ef4444',
            borderUpColor: '#22c55e', borderDownColor: '#ef4444',
            wickUpColor: '#22c55e', wickDownColor: '#ef4444',
          });
          candles.setData(ex.ohlcv);
          candles.createPriceLine({
            price: ex.strike, color: '#f59e0b', lineWidth: 1,
            lineStyle: LightweightCharts.LineStyle.Dashed, title: 'Strike $' + ex.strike.toFixed(2),
          });
          candles.setMarkers([
            { time: ex.entry_date, position: 'belowBar', color: '#22c55e', shape: 'arrowUp', text: 'Buy Call' },
            { time: ex.exit_date,  position: 'aboveBar', color: '#f59e0b', shape: 'arrowDown', text: 'Exit' },
          ]);
          chart.timeScale().fitContent();

          // Chain table
          let chainHtml = '<table class="opt-table"><tr>' +
            '<th>Call Price</th><th>Call Δ</th><th>Strike</th><th>Put Δ</th><th>Put Price</th></tr>';
          ex.chain.forEach(row => {
            chainHtml += '<tr class="' + (row.is_strike ? 'atm-row' : '') + '">' +
              '<td style="color:#22c55e">$' + row.call_price.toFixed(2) + '</td>' +
              '<td style="color:#666">' + row.call_delta.toFixed(3) + '</td>' +
              '<td style="font-weight:700">' + (row.is_strike ? '→ ' : '') + '$' + row.strike.toFixed(2) + '</td>' +
              '<td style="color:#666">' + row.put_delta.toFixed(3) + '</td>' +
              '<td style="color:#ef4444">$' + row.put_price.toFixed(2) + '</td>' +
              '</tr>';
          });
          chainHtml += '</table>';
          document.getElementById('ex-chain-' + i).innerHTML = chainHtml;

          // Walkthrough table
          let wtHtml = '<table class="opt-table"><tr>' +
            '<th>Date</th><th>Spot</th><th>Days to Exp</th><th>Option Price</th><th>Delta</th><th>Theta/day</th><th>P&amp;L</th><th>P&amp;L %</th></tr>';
          ex.walkthrough.forEach((row, j) => {
            const pnlColor = row.pnl >= 0 ? '#22c55e' : '#ef4444';
            const pnlSign = row.pnl >= 0 ? '+' : '';
            wtHtml += '<tr>' +
              '<td>' + row.date + (j === 0 ? ' (entry)' : (j === ex.walkthrough.length - 1 ? ' (exit)' : '')) + '</td>' +
              '<td>$' + row.spot.toFixed(2) + '</td>' +
              '<td style="color:#666">' + row.dte + '</td>' +
              '<td>$' + row.price.toFixed(2) + '</td>' +
              '<td style="color:#666">' + row.delta.toFixed(3) + '</td>' +
              '<td style="color:#666">' + row.theta.toFixed(3) + '</td>' +
              '<td style="color:' + pnlColor + ';font-weight:600">' + pnlSign + '$' + row.pnl.toFixed(2) + '</td>' +
              '<td style="color:' + pnlColor + '">' + pnlSign + row.pnl_pct.toFixed(1) + '%</td>' +
              '</tr>';
          });
          wtHtml += '</table>';
          document.getElementById('ex-walk-' + i).innerHTML = wtHtml;

          // P&L chart
          const pnlChart = LightweightCharts.createChart(document.getElementById('ex-pnl-' + i), {
            layout: { background: { color: '#0a0c14' }, textColor: '#888' },
            grid: { vertLines: { color: '#1a1d2e' }, horzLines: { color: '#1a1d2e' } },
            rightPriceScale: { borderColor: '#2a2d3e' },
            timeScale: { borderColor: '#2a2d3e', timeVisible: true },
          });
          const pnlSeries = pnlChart.addHistogramSeries({ priceFormat: { type: 'price', precision: 0 } });
          pnlSeries.setData(ex.walkthrough.map(row => ({
            time: row.date, value: row.pnl, color: row.pnl >= 0 ? '#22c55e88' : '#ef444488',
          })));
          pnlChart.timeScale().fitContent();
        });
      })
      .catch(e => { document.getElementById('options-status').textContent = 'Failed to load: ' + e; });
    </script>
    """

    return page_wrap('How It Works', 'howitworks', content)


# ─── Dividend Picks ───────────────────────────────────────────────────────────

@app.route('/dividend')
def dividend_page():
    stocks = get_all_dividend_stocks()
    admin  = is_admin()

    # Get latest prices from DB — check both US (prices) and ASX (asx_prices) tables
    tickers = [s['ticker'] for s in stocks]
    prices  = {}
    if tickers:
        try:
            conn = get_connection()
            fmt  = ','.join(['%s'] * len(tickers))
            with conn.cursor() as cur:
                # US prices table
                cur.execute(f"""
                    SELECT p.ticker, p.close
                    FROM prices p
                    INNER JOIN (
                        SELECT ticker, MAX(date) AS md FROM prices
                        WHERE ticker IN ({fmt}) GROUP BY ticker
                    ) latest ON p.ticker=latest.ticker AND p.date=latest.md
                """, tickers)
                for t, c in cur.fetchall():
                    prices[t] = float(c)
                # ASX prices table (fills in any not found above)
                cur.execute(f"""
                    SELECT p.ticker, p.close
                    FROM asx_prices p
                    INNER JOIN (
                        SELECT ticker, MAX(date) AS md FROM asx_prices
                        WHERE ticker IN ({fmt}) GROUP BY ticker
                    ) latest ON p.ticker=latest.ticker AND p.date=latest.md
                """, tickers)
                for t, c in cur.fetchall():
                    if t not in prices:
                        prices[t] = float(c)
            conn.close()
        except Exception:
            pass

    # ── Stock list rows ────────────────────────────────────────────────────────
    list_rows = ''
    for s in stocks:
        price    = prices.get(s['ticker'])
        price_td = f'${price:,.2f}' if price else '—'
        yld      = f"{s['dividend_yield']:.2f}%" if s['dividend_yield'] else '—'
        yrs      = str(s['years_div_growth']) if s['years_div_growth'] else '—'
        target   = f"${s['target_price']:,.2f}" if s['target_price'] else '—'
        sector   = s['sector'] or ''
        edit_btn = f'<a href="/dividend/edit/{s["id"]}" style="color:#60a5fa;font-size:.75rem;margin-left:8px">edit</a>' if admin else ''
        sticker  = s['ticker']
        del_btn  = f'<a href="/dividend/delete/{s["id"]}" onclick="return confirm(\'Remove {sticker}?\')" style="color:#ef4444;font-size:.75rem;margin-left:6px">×</a>' if admin else ''

        list_rows += f"""
        <tr class="div-row" data-id="{s['id']}" onclick="showThesis({s['id']})">
          <td style="padding:12px 14px;font-weight:700;color:#e0e0e0;white-space:nowrap">
            {s['ticker']}{edit_btn}{del_btn}
          </td>
          <td style="padding:12px 8px;color:#aaa;font-size:.82rem">{s['company']}</td>
          <td style="padding:12px 8px;color:#888;font-size:.78rem">{sector}</td>
          <td style="padding:12px 8px;color:#22c55e;font-weight:600;text-align:right">{yld}</td>
          <td style="padding:12px 8px;color:#60a5fa;text-align:right">{price_td}</td>
          <td style="padding:12px 8px;color:#f59e0b;text-align:right">{target}</td>
          <td style="padding:12px 8px;color:#888;text-align:center;font-size:.8rem">{yrs} yrs</td>
        </tr>"""

    if not list_rows:
        list_rows = '<tr><td colspan="7" style="padding:24px;text-align:center;color:#555">No stocks added yet.</td></tr>'

    # ── Thesis panels (hidden, shown on click) ─────────────────────────────────
    thesis_panels = ''
    for s in stocks:
        points = [
            ('Business Moat',        s['thesis_moat'],     '#818cf8'),
            ('Dividend Track Record', s['thesis_dividend'], '#22c55e'),
            ('Payout Sustainability', s['thesis_sustain'],  '#f59e0b'),
            ('Price Trend',           s['thesis_trend'],    '#60a5fa'),
            ('Why Now',               s['thesis_why_now'],  '#f472b6'),
        ]
        pts_html = ''
        for title, body, color in points:
            txt = body if body else '<span style="color:#555;font-style:italic">Not yet written.</span>'
            pts_html += f"""
            <div style="margin-bottom:18px">
              <div style="font-size:.7rem;font-weight:700;letter-spacing:.08em;color:{color};text-transform:uppercase;margin-bottom:4px">{title}</div>
              <div style="color:#ccc;font-size:.88rem;line-height:1.6">{txt}</div>
            </div>"""

        price    = prices.get(s['ticker'])
        yld      = f"{s['dividend_yield']:.2f}%" if s['dividend_yield'] else '—'
        pr       = f"{s['payout_ratio']:.0f}%" if s['payout_ratio'] else '—'
        yrs      = f"{s['years_div_growth']} years" if s['years_div_growth'] else '—'
        price_td = f'${price:,.2f}' if price else '—'
        target   = f"${s['target_price']:,.2f}" if s['target_price'] else '—'
        edit_lnk  = f'<a href="/dividend/edit/{s["id"]}" class="btn btn-blue" style="font-size:.78rem;padding:5px 14px">Edit Thesis</a>' if admin else ''
        chart_img = f'<img src="/dividend/image/{s["image_path"]}" onclick="openLightbox(this.src)" style="width:100%;border-radius:8px;margin-bottom:18px;border:1px solid #2a2d3e;cursor:zoom-in">' if s.get('image_path') else ''

        thesis_panels += f"""
        <div id="thesis-{s['id']}" class="thesis-panel" style="display:none">
          <div style="display:flex;justify-content:space-between;align-items:flex-start;margin-bottom:18px">
            <div>
              <div style="font-size:1.4rem;font-weight:800;color:#e0e0e0">{s['ticker']}</div>
              <div style="color:#888;font-size:.85rem">{s['company']}</div>
              <div style="color:#555;font-size:.75rem;margin-top:2px">{s['sector']}</div>
            </div>
            <div style="text-align:right">
              <div style="font-size:1.1rem;font-weight:700;color:#60a5fa">{price_td}</div>
              <div style="color:#22c55e;font-size:.85rem;font-weight:600">Yield {yld}</div>
              <div style="color:#aaa;font-size:.75rem">Target {target}</div>
            </div>
          </div>
          {chart_img}
          <div style="display:grid;grid-template-columns:1fr 1fr 1fr;gap:10px;margin-bottom:20px">
            <div class="card" style="padding:10px 14px;text-align:center">
              <div style="font-size:.68rem;color:#555;text-transform:uppercase;letter-spacing:.06em">Div Yield</div>
              <div style="font-size:1.1rem;font-weight:700;color:#22c55e">{yld}</div>
            </div>
            <div class="card" style="padding:10px 14px;text-align:center">
              <div style="font-size:.68rem;color:#555;text-transform:uppercase;letter-spacing:.06em">Payout Ratio</div>
              <div style="font-size:1.1rem;font-weight:700;color:#f59e0b">{pr}</div>
            </div>
            <div class="card" style="padding:10px 14px;text-align:center">
              <div style="font-size:.68rem;color:#555;text-transform:uppercase;letter-spacing:.06em">Div Growth</div>
              <div style="font-size:1.1rem;font-weight:700;color:#818cf8">{yrs}</div>
            </div>
          </div>
          <h3 style="font-size:.9rem;color:#555;margin-bottom:14px;text-transform:uppercase;letter-spacing:.08em">Jimmy's Thesis</h3>
          {pts_html}
          <div style="margin-top:16px">{edit_lnk}</div>
        </div>"""

    add_btn = '<a href="/dividend/add" class="btn btn-green" style="margin-bottom:16px">+ Add Stock</a>' if admin else ''

    content = f"""
    <style>
      .div-row {{ cursor:pointer; border-bottom:1px solid #151820; transition:background .15s; }}
      .div-row:hover td {{ background:#1a1d2e; }}
      .div-row.active td {{ background:#1f2235; }}
      .thesis-panel {{ background:#13151f; border:1px solid #2a2d3e; border-radius:10px; padding:22px; }}
    </style>

    <div style="display:flex;gap:20px;align-items:flex-start">

      <!-- Left: stock list -->
      <div style="flex:1;min-width:0">
        <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:12px">
          <h2 style="margin:0">Long-Term Dividend Picks</h2>
          {add_btn}
        </div>
        <p style="color:#666;font-size:.83rem;margin-bottom:16px">
          Stocks selected for long-term holding (10–20 years). Click any row to read the thesis.
        </p>
        <div class="card" style="padding:0;overflow:hidden">
          <table style="width:100%;border-collapse:collapse;font-size:.84rem">
            <thead>
              <tr style="border-bottom:2px solid #2a2d3e">
                <th style="text-align:left;padding:10px 14px;color:#555;font-weight:500">Ticker</th>
                <th style="text-align:left;padding:10px 8px;color:#555;font-weight:500">Company</th>
                <th style="text-align:left;padding:10px 8px;color:#555;font-weight:500">Sector</th>
                <th style="text-align:right;padding:10px 8px;color:#555;font-weight:500">Yield</th>
                <th style="text-align:right;padding:10px 8px;color:#555;font-weight:500">Price</th>
                <th style="text-align:right;padding:10px 8px;color:#555;font-weight:500">Target</th>
                <th style="text-align:center;padding:10px 8px;color:#555;font-weight:500">Div Growth</th>
              </tr>
            </thead>
            <tbody>{list_rows}</tbody>
          </table>
        </div>
      </div>

      <!-- Lightbox overlay -->
      <div id="div-lightbox" onclick="closeLightbox()" style="display:none;position:fixed;inset:0;background:rgba(0,0,0,.92);z-index:9999;cursor:zoom-out;align-items:center;justify-content:center">
        <img id="div-lightbox-img" src="" style="max-width:92vw;max-height:92vh;border-radius:8px;box-shadow:0 0 60px rgba(0,0,0,.8)">
      </div>

      <!-- Right: thesis panel -->
      <div style="width:380px;flex-shrink:0;position:sticky;top:80px">
        <div id="thesis-placeholder" style="background:#13151f;border:1px solid #1e2130;border-radius:10px;padding:40px 24px;text-align:center;color:#444">
          <div style="font-size:2rem;margin-bottom:10px">📋</div>
          <div>Click a stock to read the thesis</div>
        </div>
        {thesis_panels}
      </div>

    </div>

    <script>
      function showThesis(id) {{
        document.querySelectorAll('.thesis-panel').forEach(p => p.style.display = 'none');
        document.querySelectorAll('.div-row').forEach(r => r.classList.remove('active'));
        document.getElementById('thesis-placeholder').style.display = 'none';
        document.getElementById('thesis-' + id).style.display = 'block';
        document.querySelector('.div-row[data-id="' + id + '"]').classList.add('active');
      }}
      function openLightbox(src) {{
        var lb = document.getElementById('div-lightbox');
        document.getElementById('div-lightbox-img').src = src;
        lb.style.display = 'flex';
      }}
      function closeLightbox() {{
        document.getElementById('div-lightbox').style.display = 'none';
      }}
      document.addEventListener('keydown', function(e) {{
        if (e.key === 'Escape') closeLightbox();
      }});
    </script>
    """

    return page_wrap('Dividend Picks', 'dividend', content)


def _handle_dividend_image():
    """Save uploaded chart image, return filename or None."""
    file = request.files.get('chart_image')
    if file and file.filename:
        ext      = os.path.splitext(file.filename)[1].lower()
        filename = f"div_{uuid.uuid4().hex}{ext}"
        os.makedirs(UPLOADS_DIR, exist_ok=True)
        file.save(os.path.join(UPLOADS_DIR, filename))
        return filename
    return None


@app.route('/dividend/add', methods=['GET', 'POST'])
def dividend_add():
    if not is_admin():
        return redirect('/dividend')
    error = ''
    if request.method == 'POST':
        image_path = _handle_dividend_image()
        ok, err = upsert_dividend_stock(
            ticker=request.form.get('ticker','').strip(),
            company=request.form.get('company','').strip(),
            sector=request.form.get('sector','').strip(),
            dividend_yield=request.form.get('dividend_yield') or None,
            payout_ratio=request.form.get('payout_ratio') or None,
            years_div_growth=request.form.get('years_div_growth') or None,
            target_price=request.form.get('target_price') or None,
            thesis_moat=request.form.get('thesis_moat','').strip(),
            thesis_dividend=request.form.get('thesis_dividend','').strip(),
            thesis_sustain=request.form.get('thesis_sustain','').strip(),
            thesis_trend=request.form.get('thesis_trend','').strip(),
            thesis_why_now=request.form.get('thesis_why_now','').strip(),
            image_path=image_path,
            display_order=int(request.form.get('display_order') or 0),
        )
        if ok:
            return redirect('/dividend')
        error = err
    return page_wrap('Add Dividend Stock', 'dividend', _dividend_form(error=error))


@app.route('/dividend/edit/<int:stock_id>', methods=['GET', 'POST'])
def dividend_edit(stock_id):
    if not is_admin():
        return redirect('/dividend')
    stock = get_dividend_stock(stock_id)
    if not stock:
        return redirect('/dividend')
    error = ''
    if request.method == 'POST':
        image_path = _handle_dividend_image()
        ok, err = upsert_dividend_stock(
            ticker=request.form.get('ticker','').strip(),
            company=request.form.get('company','').strip(),
            sector=request.form.get('sector','').strip(),
            dividend_yield=request.form.get('dividend_yield') or None,
            payout_ratio=request.form.get('payout_ratio') or None,
            years_div_growth=request.form.get('years_div_growth') or None,
            target_price=request.form.get('target_price') or None,
            thesis_moat=request.form.get('thesis_moat','').strip(),
            thesis_dividend=request.form.get('thesis_dividend','').strip(),
            thesis_sustain=request.form.get('thesis_sustain','').strip(),
            thesis_trend=request.form.get('thesis_trend','').strip(),
            thesis_why_now=request.form.get('thesis_why_now','').strip(),
            image_path=image_path,
            display_order=int(request.form.get('display_order') or 0),
            stock_id=stock_id,
        )
        if ok:
            return redirect('/dividend')
        error = err
    return page_wrap('Edit Dividend Stock', 'dividend', _dividend_form(stock=stock, error=error))


@app.route('/dividend/delete/<int:stock_id>')
def dividend_delete(stock_id):
    if not is_admin():
        return redirect('/dividend')
    delete_dividend_stock(stock_id)
    return redirect('/dividend')


@app.route('/dividend/image/<filename>')
def dividend_image(filename):
    return send_from_directory(UPLOADS_DIR, filename)


def _dividend_form(stock=None, error=''):
    s = stock or {}
    def v(k, default=''): return s.get(k, default) or default
    def textarea(name, label, color, placeholder):
        return f"""
        <div style="margin-bottom:16px">
          <label style="display:block;font-size:.75rem;font-weight:700;color:{color};
                        text-transform:uppercase;letter-spacing:.08em;margin-bottom:6px">{label}</label>
          <textarea name="{name}" rows="4" placeholder="{placeholder}"
            style="width:100%;background:#0f1117;border:1px solid #2a2d3e;border-radius:6px;
                   color:#e0e0e0;padding:10px 12px;font-size:.85rem;resize:vertical;box-sizing:border-box"
          >{v(name)}</textarea>
        </div>"""

    err_html = f'<div style="color:#ef4444;margin-bottom:12px">{error}</div>' if error else ''
    title    = 'Edit Stock' if stock else 'Add Stock'

    return f"""
    <h2>{title}</h2>
    {err_html}
    <form method="POST" enctype="multipart/form-data" style="max-width:700px">
      <div style="display:grid;grid-template-columns:1fr 2fr;gap:12px;margin-bottom:16px">
        <div>
          <label style="color:#888;font-size:.78rem">Ticker</label>
          <input name="ticker" value="{v('ticker')}" required
            style="width:100%;background:#0f1117;border:1px solid #2a2d3e;border-radius:6px;
                   color:#e0e0e0;padding:9px 12px;font-size:.9rem;box-sizing:border-box">
        </div>
        <div>
          <label style="color:#888;font-size:.78rem">Company Name</label>
          <input name="company" value="{v('company')}" required
            style="width:100%;background:#0f1117;border:1px solid #2a2d3e;border-radius:6px;
                   color:#e0e0e0;padding:9px 12px;font-size:.9rem;box-sizing:border-box">
        </div>
      </div>
      <div style="display:grid;grid-template-columns:1fr 1fr 1fr 1fr 1fr;gap:12px;margin-bottom:20px">
        <div>
          <label style="color:#888;font-size:.78rem">Sector</label>
          <input name="sector" value="{v('sector')}"
            style="width:100%;background:#0f1117;border:1px solid #2a2d3e;border-radius:6px;
                   color:#e0e0e0;padding:9px 12px;font-size:.85rem;box-sizing:border-box">
        </div>
        <div>
          <label style="color:#888;font-size:.78rem">Div Yield %</label>
          <input name="dividend_yield" type="number" step="0.01" value="{v('dividend_yield')}"
            style="width:100%;background:#0f1117;border:1px solid #2a2d3e;border-radius:6px;
                   color:#e0e0e0;padding:9px 12px;font-size:.85rem;box-sizing:border-box">
        </div>
        <div>
          <label style="color:#888;font-size:.78rem">Payout Ratio %</label>
          <input name="payout_ratio" type="number" step="0.1" value="{v('payout_ratio')}"
            style="width:100%;background:#0f1117;border:1px solid #2a2d3e;border-radius:6px;
                   color:#e0e0e0;padding:9px 12px;font-size:.85rem;box-sizing:border-box">
        </div>
        <div>
          <label style="color:#888;font-size:.78rem">Years Div Growth</label>
          <input name="years_div_growth" type="number" value="{v('years_div_growth')}"
            style="width:100%;background:#0f1117;border:1px solid #2a2d3e;border-radius:6px;
                   color:#e0e0e0;padding:9px 12px;font-size:.85rem;box-sizing:border-box">
        </div>
        <div>
          <label style="color:#888;font-size:.78rem">Target Price</label>
          <input name="target_price" type="number" step="0.01" value="{v('target_price')}"
            style="width:100%;background:#0f1117;border:1px solid #2a2d3e;border-radius:6px;
                   color:#e0e0e0;padding:9px 12px;font-size:.85rem;box-sizing:border-box">
        </div>
      </div>

      <h3 style="color:#555;font-size:.8rem;text-transform:uppercase;letter-spacing:.1em;margin-bottom:16px">
        Jimmy's 5-Point Thesis
      </h3>
      {textarea('thesis_moat',     'Business Moat',         '#818cf8', 'Does it have pricing power? Will it still exist in 20 years?')}
      {textarea('thesis_dividend', 'Dividend Track Record',  '#22c55e', 'How many years of consecutive dividend growth?')}
      {textarea('thesis_sustain',  'Payout Sustainability',  '#f59e0b', 'Payout ratio healthy? Free cash flow covers it?')}
      {textarea('thesis_trend',    'Price Trend',            '#60a5fa', 'Is the stock price trending up over 10 years?')}
      {textarea('thesis_why_now',  'Why Now',                '#f472b6', 'Is it at a good entry point? Why buy at this price?')}

      <div style="margin-bottom:20px">
        <label style="display:block;font-size:.75rem;font-weight:700;color:#aaa;
                      text-transform:uppercase;letter-spacing:.08em;margin-bottom:6px">Chart Image</label>
        {'<img src="/dividend/image/' + v('image_path') + '" style="width:100%;border-radius:6px;margin-bottom:8px;border:1px solid #2a2d3e">' if v('image_path') else ''}
        <input type="file" name="chart_image" accept="image/*"
          style="color:#aaa;font-size:.83rem">
        <div style="color:#555;font-size:.75rem;margin-top:4px">Upload a screenshot of your chart (PNG, JPG). Leave blank to keep existing image.</div>
      </div>

      <div style="display:flex;gap:10px;margin-top:8px">
        <button type="submit" class="btn btn-green">Save Stock</button>
        <a href="/dividend" class="btn" style="background:#2a2d3e;color:#aaa">Cancel</a>
      </div>
    </form>
    """


# ─── Admin Analytics ──────────────────────────────────────────────────────────

@app.route('/admin/analytics')
def admin_analytics():
    if not is_admin():
        return redirect('/')

    s = get_user_stats()
    users = s['users']

    # Build user rows
    user_rows = ''
    for u in users:
        q_color = '#60a5fa' if u['q_count'] > 0 else '#555'
        user_rows += f"""<tr>
          <td style="color:#aaa;font-size:.78rem">{u['id']}</td>
          <td><strong style="color:#e0e0e0">{u['username']}</strong></td>
          <td style="color:#777;font-size:.83rem">{u['email']}</td>
          <td style="color:#aaa;font-size:.83rem">{u['created_date']}</td>
          <td style="color:{q_color};font-weight:700;text-align:center">{u['q_count']}</td>
          <td style="color:#777;font-size:.83rem">{u['last_question']}</td>
        </tr>"""

    content = f"""
    <style>
      .a-table {{ width:100%; border-collapse:collapse; font-size:.85rem; }}
      .a-table th {{ text-align:left; padding:9px 12px; color:#555; border-bottom:1px solid #2a2d3e; font-weight:500; }}
      .a-table td {{ padding:9px 12px; border-bottom:1px solid #151820; }}
      .a-table tr:hover td {{ background:#1f2235; }}
    </style>

    <!-- Summary stats -->
    <div class="grid4" style="margin-bottom:24px">
      <div class="card">
        <div class="stat-label">Total Users</div>
        <div class="stat-value">{s['total_users']}</div>
        <div class="stat-sub">registered accounts</div>
      </div>
      <div class="card">
        <div class="stat-label">New This Week</div>
        <div class="stat-value" style="color:#22c55e">{s['new_this_week']}</div>
        <div class="stat-sub">last 7 days</div>
      </div>
      <div class="card">
        <div class="stat-label">Questions Asked</div>
        <div class="stat-value">{s['total_questions']}</div>
        <div class="stat-sub">{s['answered']} answered · {s['pending']} pending</div>
      </div>
      <div class="card">
        <div class="stat-label">Pending Questions</div>
        <div class="stat-value" style="color:{'#f59e0b' if s['pending'] > 0 else '#22c55e'}">{s['pending']}</div>
        <div class="stat-sub"><a href="/ask">Go to Ask Jimmy →</a></div>
      </div>
    </div>

    <!-- User table -->
    <section>
      <h2>Registered Users ({s['total_users']})</h2>
      {'<table class="a-table"><thead><tr><th>#</th><th>Username</th><th>Email</th><th>Joined</th><th style="text-align:center">Questions</th><th>Last Question</th></tr></thead><tbody>' + user_rows + '</tbody></table>' if users else '<p class="note">No users registered yet.</p>'}
    </section>
    """

    return page_wrap('Analytics', 'analytics', content)


# ─── Admin Hub ────────────────────────────────────────────────────────────────

@app.route('/admin')
def admin_hub():
    if not is_admin():
        return redirect('/')

    with _job_lock:
        running   = _job_running
        jname     = _job_name
        job_auto  = _job_auto

    stats                  = get_db_stats()
    last_refresh           = get_last_refresh_date()
    refreshed_today        = already_refreshed_today()
    last_daily_update      = get_last_daily_update_date()
    daily_updated_today    = already_daily_updated_today()
    s               = get_user_stats()

    # ── Button states ─────────────────────────────────────────────────────────
    def job_btn(label, href, style='btn-blue', confirm=None):
        if running:
            return f'<span class="btn btn-off">{label}</span>'
        c = f' onclick="return confirm(\'{confirm}\')"' if confirm else ''
        return f'<a href="{href}" class="btn {style}"{c}>{label}</a>'

    refresh_btn  = job_btn('⟳ Update US & ASX Prices', '/run-refresh', 'btn-green')
    daily_btn    = job_btn('Run Daily Update', '/run-daily')
    initial_btn  = job_btn('Run Initial Download', '/run-initial', 'btn-amber',
                           'This downloads 5 years for all tickers. Takes 1–2 hours. Continue?')
    asx_dl_btn   = job_btn('Download / Update ASX Data', '/asx/download')
    channel_btn  = job_btn('▶ Run Channel Scan', '/run-scan')
    fader_btn    = job_btn('▶ Run Fader Scan', '/run-fader')
    efi_btn      = job_btn('▶ Run EFI Scan', '/run-efi')
    range_btn    = job_btn('▶ Run Range Scan', '/range/run')
    wick_btn     = job_btn('▶ Run Wick Scan', '/run-wick')
    hammer_btn   = job_btn('▶ Run Hammer Scan', '/run-hammer')
    gapdown_btn  = job_btn('▶ Run Gap Down Scan', '/run-gapdown')
    marubozu_btn = job_btn('▶ Run Marubozu Scan', '/run-marubozu')
    extreme_btn  = job_btn('▶ Run Extreme Scan', '/run-extreme')
    pchan_btn    = job_btn('▶ Run Channel Scan', '/run-channels')
    rangeosc_btn = job_btn('▶ Run Range Oscillator Scan', '/run-range-oscillator')
    swing_btn    = job_btn('▶ Run Swing Scan', '/run-swing')
    higherlow_btn = job_btn('▶ Run Higher Low Scan', '/run-higher-low')
    extremeexit_btn = job_btn('▶ Run Extreme Exit Scan', '/run-extreme-exit')
    doublebottom_btn = job_btn('▶ Run Gap Down Double Bottom Scan', '/run-doublebottom')
    recession_btn = job_btn('▶ Check Recession Watchlist', '/run-recession')

    refresh_note = f'Last updated: {last_refresh}' if last_refresh else 'Not updated today'
    daily_update_note = (
        f'Full daily update last ran: {last_daily_update}' if last_daily_update
        else 'Full daily update has not run today'
    )

    # ── Job status bar ────────────────────────────────────────────────────────
    if running:
        auto_tag = ' (auto-triggered on page load)' if job_auto else ''
        status_bar = f'<div style="background:#78350f;color:#fcd34d;padding:12px 18px;border-radius:8px;margin-bottom:24px;font-weight:600">⚙ {jname} is running{auto_tag}… <a href="/log-view" style="color:#fcd34d;margin-left:12px">View log →</a></div>'
    else:
        status_bar = '<div style="background:#052e16;color:#86efac;padding:12px 18px;border-radius:8px;margin-bottom:24px;font-weight:600">● All jobs idle</div>'

    # ── Last scan summaries ───────────────────────────────────────────────────
    ch_last   = load_last_results()
    fd_last   = load_last_fader_results()
    ef_last   = load_last_efi_results()
    wick_last   = load_last_wick_results()
    hammer_last   = load_last_hammer_results()
    gapdown_last  = load_last_gapdown_results()
    marubozu_last = load_last_marubozu_results()
    extreme_last  = load_last_extreme_results()
    pchan_last    = load_last_price_channel_results()
    rangeosc_last = load_last_range_oscillator_results()
    swing_last    = load_last_swing_results()
    higherlow_last = load_last_higher_low_results()
    extremeexit_last = load_last_extreme_exit_results()
    doublebottom_last = load_last_doublebottom_results()
    recession_last = load_last_recession_results()

    def scan_summary(last, results_url):
        if not last:
            return '<span style="color:#555;font-size:.8rem">No scan run yet</span>'
        d = last.get('scan_date','?')
        t = last.get('total', last.get('count', '?'))
        return f'<span style="color:#aaa;font-size:.8rem">Last: {d} — {t} results &nbsp;<a href="{results_url}">View →</a></span>'

    # ── User analytics rows ───────────────────────────────────────────────────
    user_rows = ''
    for u in s['users']:
        q_color = '#60a5fa' if u['q_count'] > 0 else '#555'
        user_rows += f"""<tr>
          <td style="color:#aaa;font-size:.78rem">{u['id']}</td>
          <td><strong>{u['username']}</strong></td>
          <td style="color:#777;font-size:.83rem">{u['email']}</td>
          <td style="color:#aaa;font-size:.83rem">{u['created_date']}</td>
          <td style="color:{q_color};font-weight:700;text-align:center">{u['q_count']}</td>
          <td style="color:#777;font-size:.83rem">{u['last_question']}</td>
        </tr>"""

    # ── Log preview ───────────────────────────────────────────────────────────
    log_text = get_log()
    log_tail  = '\n'.join(log_text.splitlines()[-30:])

    content = f"""
    <style>
      .admin-grid {{ display:grid; grid-template-columns:1fr 1fr; gap:20px; margin-bottom:20px; }}
      .admin-grid3 {{ display:grid; grid-template-columns:1fr 1fr 1fr; gap:20px; margin-bottom:20px; }}
      .tool-card {{ background:#1a1d2e; border:1px solid #2a2d3e; border-radius:8px; padding:20px; }}
      .tool-card h3 {{ font-size:.72rem; font-weight:600; color:#777; text-transform:uppercase;
                       letter-spacing:.06em; margin-bottom:14px; }}
      .a-table {{ width:100%; border-collapse:collapse; font-size:.85rem; }}
      .a-table th {{ text-align:left; padding:9px 12px; color:#555; border-bottom:1px solid #2a2d3e; font-weight:500; }}
      .a-table td {{ padding:9px 12px; border-bottom:1px solid #151820; }}
      .a-table tr:hover td {{ background:#1f2235; }}
    </style>

    {status_bar}

    <!-- DB stats -->
    <div class="admin-grid3" style="margin-bottom:20px">
      <div class="card">
        <div class="stat-label">Tickers in DB</div>
        <div class="stat-value">{stats['tickers']:,}</div>
        <div class="stat-sub">{stats['rows']} total rows</div>
      </div>
      <div class="card">
        <div class="stat-label">Latest Data</div>
        <div class="stat-value" style="font-size:1.2rem">{stats['latest']}</div>
        <div class="stat-sub">{refresh_note}</div>
        <div class="stat-sub" style="color:{'#4ade80' if daily_updated_today else '#f59e0b'}">{daily_update_note}</div>
      </div>
      <div class="card">
        <div class="stat-label">Registered Users</div>
        <div class="stat-value">{s['total_users']}</div>
        <div class="stat-sub">{s['new_this_week']} new this week · {s['pending']} pending questions</div>
      </div>
    </div>

    <!-- Price data + ASX -->
    <div class="admin-grid">
      <div class="tool-card">
        <h3>Price Data — US &amp; ASX</h3>
        <div class="btn-row" style="margin-bottom:10px">
          {refresh_btn}
        </div>
        <div class="btn-row" style="margin-bottom:10px">
          {daily_btn}
          {asx_dl_btn}
        </div>
        <div class="btn-row">
          {initial_btn}
        </div>
        <p class="note" style="margin-top:10px">Initial download takes 1–2 hours for all tickers.</p>
        <p class="note">Daily Update also auto-runs the first time you (logged in as admin) load any page each day, if it hasn't run yet.</p>
      </div>

      <!-- Scanners -->
      <div class="tool-card">
        <h3>Scanners</h3>
        <div style="display:grid;grid-template-columns:1fr 1fr;gap:10px">
          <div>
            <div class="btn-row" style="margin-bottom:6px">{channel_btn}</div>
            {scan_summary(ch_last, '/results')}
          </div>
          <div>
            <div class="btn-row" style="margin-bottom:6px">{fader_btn}</div>
            {scan_summary(fd_last, '/fader')}
          </div>
          <div>
            <div class="btn-row" style="margin-bottom:6px">{efi_btn}</div>
            {scan_summary(ef_last, '/efi')}
          </div>
          <div>
            <div class="btn-row" style="margin-bottom:6px">{range_btn}</div>
            {scan_summary(None, '/range')}
          </div>
          <div>
            <div class="btn-row" style="margin-bottom:6px">{wick_btn}</div>
            {scan_summary(wick_last, '/wick')}
          </div>
          <div>
            <div class="btn-row" style="margin-bottom:6px">{hammer_btn}</div>
            {scan_summary(hammer_last, '/hammer')}
          </div>
          <div>
            <div class="btn-row" style="margin-bottom:6px">{gapdown_btn}</div>
            {scan_summary(gapdown_last, '/gapdown')}
          </div>
          <div>
            <div class="btn-row" style="margin-bottom:6px">{marubozu_btn}</div>
            {scan_summary(marubozu_last, '/marubozu')}
          </div>
          <div>
            <div class="btn-row" style="margin-bottom:6px">{extreme_btn}</div>
            {scan_summary(extreme_last, '/extreme')}
          </div>
          <div>
            <div class="btn-row" style="margin-bottom:6px">{pchan_btn}</div>
            {scan_summary(pchan_last, '/channels')}
          </div>
          <div>
            <div class="btn-row" style="margin-bottom:6px">{rangeosc_btn}</div>
            {scan_summary(rangeosc_last, '/range-oscillator')}
          </div>
          <div>
            <div class="btn-row" style="margin-bottom:6px">{swing_btn}</div>
            {scan_summary(swing_last, '/swing')}
          </div>
          <div>
            <div class="btn-row" style="margin-bottom:6px">{higherlow_btn}</div>
            {scan_summary(higherlow_last, '/higher-low')}
          </div>
          <div>
            <div class="btn-row" style="margin-bottom:6px">{extremeexit_btn}</div>
            {scan_summary(extremeexit_last, '/extreme-exit')}
          </div>
          <div>
            <div class="btn-row" style="margin-bottom:6px">{doublebottom_btn}</div>
            {scan_summary(doublebottom_last, '/doublebottom')}
          </div>
          <div>
            <div class="btn-row" style="margin-bottom:6px">{recession_btn}</div>
            {scan_summary(recession_last, '/recession')}
          </div>
        </div>
      </div>
    </div>

    <!-- Scanner result links -->
    <section style="margin-bottom:20px">
      <h2>Scanner Results &amp; Tools</h2>
      <div class="btn-row">
        <a href="/results" class="btn btn-blue" style="font-size:.82rem">Channel Results</a>
        <a href="/fader"   class="btn btn-blue" style="font-size:.82rem">Fader Results</a>
        <a href="/efi"     class="btn btn-blue" style="font-size:.82rem">EFI Results</a>
        <a href="/range"   class="btn btn-blue" style="font-size:.82rem">Range Levels</a>
        <a href="/scan"    class="btn btn-blue" style="font-size:.82rem">Channel Scanner</a>
        <a href="/wick"     class="btn btn-blue" style="font-size:.82rem">Wick Scanner</a>
        <a href="/hammer"   class="btn btn-blue" style="font-size:.82rem">Hammer Scanner</a>
        <a href="/gapdown"  class="btn btn-blue" style="font-size:.82rem">Gap Down Scanner</a>
        <a href="/marubozu" class="btn btn-blue" style="font-size:.82rem">Marubozu Scanner</a>
        <a href="/extreme"  class="btn btn-blue" style="font-size:.82rem">Extreme Scanner</a>
        <a href="/channels" class="btn btn-blue" style="font-size:.82rem">Channel Scanner</a>
        <a href="/range-oscillator" class="btn btn-blue" style="font-size:.82rem">Range Oscillator Scanner</a>
        <a href="/swing" class="btn btn-blue" style="font-size:.82rem">Swing Low Scanner</a>
        <a href="/higher-low" class="btn btn-blue" style="font-size:.82rem">Higher Low Scanner</a>
        <a href="/extreme-exit" class="btn btn-blue" style="font-size:.82rem">Extreme Exit Scanner</a>
        <a href="/doublebottom" class="btn btn-blue" style="font-size:.82rem">Gap Down Double Bottom Scanner</a>
        <a href="/recession" class="btn btn-blue" style="font-size:.82rem">Recession Watchlist</a>
        <a href="/log-view" class="btn btn-blue" style="font-size:.82rem">Full Log</a>
        <a href="/ask"     class="btn btn-blue" style="font-size:.82rem">Ask Jimmy (Q&amp;A)</a>
      </div>
    </section>

    <!-- Log tail -->
    <section style="margin-bottom:20px">
      <h2>Log <span style="color:#555;font-weight:400;text-transform:none;letter-spacing:0;font-size:.75rem">(last 30 lines · <a href="/log-view">full log →</a>)</span></h2>
      <pre style="max-height:220px">{log_tail.replace('<','&lt;')}</pre>
    </section>

    <!-- Users -->
    <section>
      <h2>Registered Users ({s['total_users']}) &nbsp;
        <span style="color:{'#f59e0b' if s['pending']>0 else '#555'};font-weight:400;text-transform:none;letter-spacing:0;font-size:.78rem">
          {f'{s["pending"]} pending questions — <a href="/ask">answer →</a>' if s['pending'] else 'No pending questions'}
        </span>
      </h2>
      {'<table class="a-table"><thead><tr><th>#</th><th>Username</th><th>Email</th><th>Joined</th><th style="text-align:center">Questions</th><th>Last Question</th></tr></thead><tbody>' + user_rows + '</tbody></table>' if user_rows else '<p class="note">No users registered yet.</p>'}
    </section>
    """

    return page_wrap('Admin', 'admin', content, auto_refresh=running)


if __name__ == '__main__':
    app.run(debug=True)
