"""
DB DAILY UPDATE
===============
Checks the database for the last date stored per ticker,
downloads only the new rows from yfinance, and inserts them.

Run this every day after market close (schedule on PythonAnywhere).

Usage:
    python db_daily_update.py
"""

import yfinance as yf
import pandas as pd
import pymysql
import os
from datetime import datetime, timedelta, date

import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from db_config import DB_HOST, DB_USER, DB_PASSWORD, DB_NAME, DB_PORT

TICKER_FILE  = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'CSV', '5000.csv')
SKIP_FILE    = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'skip_tickers.txt')


def load_skip_list():
    if not os.path.exists(SKIP_FILE):
        return set()
    with open(SKIP_FILE, 'r') as f:
        return set(line.strip().upper() for line in f if line.strip())


def add_to_skip_list(ticker):
    with open(SKIP_FILE, 'a') as f:
        f.write(ticker.upper() + '\n')


def remove_from_csv(ticker):
    """Remove a ticker row from 5000.csv."""
    try:
        df = pd.read_csv(TICKER_FILE)
        col = 'Ticker' if 'Ticker' in df.columns else df.columns[0]
        before = len(df)
        df = df[df[col].str.upper() != ticker.upper()]
        if len(df) < before:
            df.to_csv(TICKER_FILE, index=False)
    except Exception:
        pass


def get_connection():
    return pymysql.connect(
        host=DB_HOST,
        user=DB_USER,
        password=DB_PASSWORD,
        database=DB_NAME,
        port=DB_PORT,
        charset='utf8mb4'
    )


def get_last_dates(conn, tickers):
    """
    Returns a dict of {ticker: last_date} for all tickers in one query.
    Tickers with no data in the DB will not appear in the dict.
    """
    placeholders = ', '.join(['%s'] * len(tickers))
    sql = f"""
        SELECT ticker, MAX(date) as last_date
        FROM prices
        WHERE ticker IN ({placeholders})
        GROUP BY ticker
    """
    with conn.cursor() as cursor:
        cursor.execute(sql, tickers)
        results = cursor.fetchall()
    return {row[0]: row[1] for row in results}


def insert_rows(conn, ticker, df):
    """Insert new OHLCV rows for a ticker."""
    if df.empty:
        return 0

    if isinstance(df.columns, pd.MultiIndex):
        df.columns = df.columns.get_level_values(0)

    df = df[['Open', 'High', 'Low', 'Close', 'Volume']].copy()
    df.index = pd.to_datetime(df.index).date

    rows = []
    for dt, row in df.iterrows():
        rows.append((
            ticker.upper(),
            str(dt),
            float(row['Open'])   if not pd.isna(row['Open'])   else None,
            float(row['High'])   if not pd.isna(row['High'])   else None,
            float(row['Low'])    if not pd.isna(row['Low'])    else None,
            float(row['Close'])  if not pd.isna(row['Close'])  else None,
            int(row['Volume'])   if not pd.isna(row['Volume']) else None,
        ))

    sql = """
        INSERT INTO prices (ticker, date, open, high, low, close, volume)
        VALUES (%s, %s, %s, %s, %s, %s, %s)
        ON DUPLICATE KEY UPDATE
            open   = VALUES(open),
            high   = VALUES(high),
            low    = VALUES(low),
            close  = VALUES(close),
            volume = VALUES(volume)
    """

    with conn.cursor() as cursor:
        cursor.executemany(sql, rows)
    conn.commit()
    return len(rows)


def main():
    print("=" * 70)
    print("DB DAILY UPDATE")
    print("=" * 70)
    print(f"Started: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print()

    # Read ticker list
    tickers_df = pd.read_csv(TICKER_FILE)
    if 'Ticker' in tickers_df.columns:
        tickers = tickers_df['Ticker'].tolist()
    else:
        tickers = tickers_df.iloc[:, 0].tolist()

    # Sector / industry ETFs for the Rotation page (IGV, ITA, KIE…) aren't all in
    # 5000.csv but need to stay current, so they're always included
    from db_rotation import ALL_ETFS
    tickers += [t for t in ALL_ETFS if t not in set(tickers)]

    skip_list = load_skip_list()
    tickers = [t for t in tickers if t.upper() not in skip_list]

    print(f"Tickers to check: {len(tickers)} ({len(skip_list)} skipped — delisted/no data)")

    conn = get_connection()

    # Get last stored date for every ticker in one DB query
    last_dates = get_last_dates(conn, tickers)
    today = date.today()

    up_to_date = 0
    updated    = 0
    new_ticker = 0
    errors     = 0
    deleted    = 0

    # A ticker is considered delisted if its last DB date is > 30 days ago
    # and yfinance returns no data for it.
    DELIST_THRESHOLD_DAYS = 30

    for i, ticker in enumerate(tickers, 1):
        try:
            last_date = last_dates.get(ticker.upper())

            if last_date is None:
                # Ticker not in DB at all - download 5 years
                start = (datetime.now() - timedelta(days=1825)).date()
                print(f"[{i}/{len(tickers)}] {ticker}: not in DB, downloading 5 years...")
                new_ticker += 1
            else:
                start = last_date + timedelta(days=1)
                if start >= today:
                    print(f"[{i}/{len(tickers)}] {ticker}: up to date")
                    up_to_date += 1
                    continue

            new_data = yf.download(
                ticker,
                start=start.strftime('%Y-%m-%d'),
                end=today.strftime('%Y-%m-%d'),
                interval="1d",
                auto_adjust=True,
                progress=False
            )

            if new_data.empty:
                if last_date is None:
                    # Never in DB and no yfinance data — skip forever
                    add_to_skip_list(ticker)
                    remove_from_csv(ticker)
                    print(f"[{i}/{len(tickers)}] {ticker}: not found on yfinance — removed from 5000.csv")
                elif (today - last_date).days > DELIST_THRESHOLD_DAYS:
                    # In DB but data is stale — delete and skip forever
                    with conn.cursor() as cursor:
                        cursor.execute("DELETE FROM prices WHERE ticker = %s", (ticker.upper(),))
                    conn.commit()
                    add_to_skip_list(ticker)
                    remove_from_csv(ticker)
                    print(f"[{i}/{len(tickers)}] {ticker}: DELETED (no data for {(today - last_date).days} days) — removed from 5000.csv")
                    deleted += 1
                else:
                    print(f"[{i}/{len(tickers)}] {ticker}: no new data")
                continue

            rows = insert_rows(conn, ticker, new_data)
            print(f"[{i}/{len(tickers)}] {ticker}: inserted {rows} new rows")
            updated += 1

        except Exception as e:
            print(f"[{i}/{len(tickers)}] {ticker}: ERROR - {str(e)[:60]}")
            errors += 1

        # Reconnect every 500 tickers to avoid timeout
        if i % 500 == 0:
            conn.close()
            conn = get_connection()
            remaining = tickers[i:]
            last_dates.update(get_last_dates(conn, remaining))
            print(f"\n--- Reconnected to DB ---\n")

    conn.close()

    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"Total tickers:   {len(tickers)}")
    print(f"Already current: {up_to_date}")
    print(f"Updated:         {updated}")
    print(f"New to DB:       {new_ticker}")
    print(f"Deleted (delisted): {deleted}")
    print(f"Errors:          {errors}")
    print(f"Completed: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print("=" * 70)


if __name__ == "__main__":
    main()
