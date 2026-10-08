import os
import time
import re
import uuid
import json
import io
import requests
import lxml.html as lxml_html
import base64
from datetime import datetime, timedelta
from threading import Lock
import threading
import sqlite3
import pandas as pd
import numpy as np
from flask import Flask, render_template, request, jsonify, session, url_for, flash, redirect, Response, send_file

from selenium import webdriver
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.common.by import By
from selenium.webdriver.common.keys import Keys
from selenium.webdriver.support.ui import Select
from selenium.webdriver.support import expected_conditions as EC
from selenium.common.exceptions import NoSuchElementException, WebDriverException, TimeoutException

# Import FPDF for Catalogue Correction
try:
    from fpdf import FPDF
    FPDF_AVAILABLE = True
except ImportError:
    FPDF_AVAILABLE = False
    print("WARNING: 'fpdf' library not found. PDF generation will be skipped. Run 'pip install fpdf'.")

# --- ★ CONFIGURATION ★ ---
ENABLE_WID_SCAN = True 
INVENTORY_REFRESH_HOURS = 12
SESSION_TIMEOUT_MINUTES = 120   # inactivity timeout (rolls forward on every request)
ALLOW_AUDIT_REDO = True   # True: box already audited -> popup offers "redo"; False: popup is informational only, no redo allowed

# Serialized FSN capture (NCOB Box Audit only): scanning an EAN whose FSN is "serialized"
# pops up a WSN / IMEI1 (Serialized Number, mandatory) / IMEI2 (optional) capture form.
# ENABLE_SERIALIZED_FSN_CSV=True  -> FSN is looked up against serialized_fsn.csv (exact match).
# ENABLE_SERIALIZED_FSN_CSV=False -> FSN (already resolved via Inventory.csv/scraped box data,
#                                    same as normal EAN matching) is checked against the prefixes
#                                    below instead. Flip to True once serialized_fsn.csv exists.
ENABLE_SERIALIZED_FSN_CSV = True
SERIALIZED_FSN_PREFIXES = ["MOB","COM"]   # used only while the flag above is False
MOBILE_FSN_PREFIX = "MOB"   # prefix fallback if a serialized_fsn.csv row has no Vertical value
MOBILE_VERTICAL_CODE = "mobile"   # value expected in serialized_fsn.csv's cms_vertical column for mobiles

# NCOB Box Audit scraping is serviced by a small shared pool of Selenium sessions
# instead of one personal session per logged-in auditor (which was overwhelming the
# host with Chrome processes once several auditors worked at once). The pool is
# filled by the first NCOB_POOL_SIZE successful logins each day; everyone after that
# still has their credentials verified the same way at login, but no personal browser
# is kept running for them - NCOB scans are serviced by the shared pool instead.
NCOB_POOL_SIZE = 3
# -------------------------

app = Flask(__name__)
app.secret_key = "qpex-integrated-production-key"

# --- ★ SESSION PERSISTENCE (keep users logged in for the whole shift) ★ ---
# The login cookie is permanent with a rolling expiry equal to the inactivity
# window. SESSION_REFRESH_EACH_REQUEST re-issues the cookie on every request, so
# an ACTIVE user never gets logged out mid-shift; the session only closes after
# SESSION_TIMEOUT_MINUTES with no activity. (Marked permanent per-request in the
# before_request hook below.)
app.permanent_session_lifetime = timedelta(minutes=SESSION_TIMEOUT_MINUTES)
app.config["SESSION_REFRESH_EACH_REQUEST"] = True

user_sessions = {}
sessions_lock = Lock()
driver_store = {}


@app.before_request
def keep_session_alive():
    """Roll the inactivity window forward on EVERY request (not just routes that
    call get_user_context), so an active user stays logged in for the full shift
    and only inactivity (no requests for SESSION_TIMEOUT_MINUTES) logs them out."""
    session.permanent = True
    uid = session.get('user_id')
    if uid:
        with sessions_lock:
            ctx = user_sessions.get(uid)
            if ctx is not None:
                ctx['last_seen'] = datetime.now()

# --- GLOBAL THREAD LOCKS FOR DB & CSV ---
db_lock = Lock()
csv_lock = Lock()

BASE_DIR = os.path.dirname(__file__)
DATABASE_NAME = os.path.join(BASE_DIR, 'audit_database.db')
INVENTORY_CSV_PATH = os.path.join(BASE_DIR, 'Inventory.csv')
SERIALIZED_FSN_CSV_PATH = os.path.join(BASE_DIR, 'serialized_fsn.csv')  # only read when ENABLE_SERIALIZED_FSN_CSV=True

# --- DIRECTORY SETUP ---
IMAGE_DIR = os.path.join(BASE_DIR, 'audit_images')
CSV_DIR = os.path.join(BASE_DIR, 'output_csv_files')
CATALOGUE_DIR = os.path.join(BASE_DIR, 'downloads', 'catalogue_correction')

os.makedirs(IMAGE_DIR, exist_ok=True)
os.makedirs(CSV_DIR, exist_ok=True)
os.makedirs(CATALOGUE_DIR, exist_ok=True)

# --- GLOBAL CATEGORY MAPPINGS ---
AUDIT_CAT_MAP = {
    'unit': 'BIN AUDIT (UNIT)',
    'bulk': 'BIN AUDIT (BULK)',
    'putlist': 'PUTLIST AUDIT',
    'picklist': 'PICKLIST AUDIT',
    'ob_audit': 'CUSTOMER OUTBOUND AUDIT',
    'hl_box_audit': 'NCOB BOX AUDIT',
    'proxy_pack': 'PROXY PACKAGING AUDIT',
    'shrink_wrap': 'SHRINKWRAP AUDIT',
    'tamper_seal': 'TAMPERSEAL AUDIT',
    'cx_misship': 'PV AUDIT'
}

def get_db_categories(search_category):
    """Maps display drop-down categories to all possible legacy and raw database values to guarantee zero records are missed."""
    category_aliases = {
        'BIN AUDIT (UNIT)': ['BIN AUDIT (UNIT)', 'UNIT'],
        'BIN AUDIT (BULK)': ['BIN AUDIT (BULK)', 'BULK'],
        'PUTLIST AUDIT': ['PUTLIST AUDIT', 'PUTLIST'],
        'PICKLIST AUDIT': ['PICKLIST AUDIT', 'PICKLIST'],
        'CUSTOMER OUTBOUND AUDIT': ['CUSTOMER OUTBOUND AUDIT', 'OB_AUDIT', 'OB AUDIT'],
        'NCOB BOX AUDIT': ['NCOB BOX AUDIT', 'HL_BOX_AUDIT'],
        'PROXY PACKAGING AUDIT': ['PROXY PACKAGING AUDIT', 'PROXY_PACK', 'PROXY PACK'],
        'SHRINKWRAP AUDIT': ['SHRINKWRAP AUDIT', 'SHRINK_WRAP', 'SHRINK WRAP'],
        'TAMPERSEAL AUDIT': ['TAMPERSEAL AUDIT', 'TAMPER_SEAL', 'TAMPER SEAL'],
        'PV AUDIT': ['PV AUDIT', 'CX_MISSHIP', 'CX MISSHIP']
    }
    return category_aliases.get(search_category, [search_category])

# --- HELPER: SAFE CSV EXPORT ---
def safe_csv_export(data_list, filename):
    if not data_list:
        return True, "No data to export"
    df = pd.DataFrame(data_list)
    path = os.path.join(CSV_DIR, filename)
    with csv_lock:
        try:
            df.to_csv(path, mode='a', header=not os.path.exists(path), index=False)
            return True, "Exported successfully"
        except PermissionError:
            backup_name = f"{filename.replace('.csv', '')}_{int(time.time())}.csv"
            backup_path = os.path.join(CSV_DIR, backup_name)
            try:
                df.to_csv(backup_path, mode='a', header=not os.path.exists(backup_path), index=False)
                return True, f"Exported successfully to backup file: {backup_name}"
            except Exception as e:
                return False, str(e)
        except Exception as e:
            return False, str(e)

def save_evidence_image(file_obj, subfolder, filename_prefix):
    if not file_obj or file_obj.filename == '':
        return ""
    safe_folder = "".join([c if c.isalnum() else "_" for c in subfolder]).strip("_").lower()
    full_dir = os.path.join(IMAGE_DIR, safe_folder)
    os.makedirs(full_dir, exist_ok=True)
    filename = f"{filename_prefix}.jpg"
    filepath = os.path.join(full_dir, filename)
    file_obj.save(filepath)
    return filepath

def generate_audit_no(audit_type, identifier):
    safe_id = re.sub(r'[^A-Za-z0-9_]', '_', str(identifier))
    short_uuid = uuid.uuid4().hex[:4]
    date_str = datetime.now().strftime('%d%m')
    return f"{audit_type}_{date_str}_{safe_id}_{short_uuid}"

# --- GLOBAL INVENTORY & AUDIT RULES SETUP ---
MASTER_INVENTORY_DF = pd.DataFrame()
LAST_INVENTORY_RELOAD_TIME = datetime.min
inventory_lock = Lock()
AUDIT_RULES = {'shrink_wrap': set(), 'tamper_seal': set()}

def load_global_inventory():
    global MASTER_INVENTORY_DF, LAST_INVENTORY_RELOAD_TIME
    if (datetime.now() - LAST_INVENTORY_RELOAD_TIME) > timedelta(hours=INVENTORY_REFRESH_HOURS):
        with inventory_lock:
            if (datetime.now() - LAST_INVENTORY_RELOAD_TIME) > timedelta(hours=INVENTORY_REFRESH_HOURS):
                try:
                    MASTER_INVENTORY_DF = pd.read_csv(INVENTORY_CSV_PATH)
                    LAST_INVENTORY_RELOAD_TIME = datetime.now()
                    print(f"Loaded Inventory.csv with {len(MASTER_INVENTORY_DF)} items.")
                except FileNotFoundError:
                    MASTER_INVENTORY_DF = pd.DataFrame()
                except Exception as e:
                    print(f"Error loading Inventory.csv: {e}")

SERIALIZED_FSN_SET = set()
SERIALIZED_FSN_VERTICAL_MAP = {}   # FSN (upper) -> Vertical (upper), populated only from serialized_fsn.csv
LAST_SERIALIZED_RELOAD_TIME = datetime.min
serialized_fsn_lock = Lock()

def load_serialized_fsns():
    """Loads serialized_fsn.csv into SERIALIZED_FSN_SET (+ SERIALIZED_FSN_VERTICAL_MAP if a
    Vertical column is present). No-op while ENABLE_SERIALIZED_FSN_CSV is False."""
    global SERIALIZED_FSN_SET, SERIALIZED_FSN_VERTICAL_MAP, LAST_SERIALIZED_RELOAD_TIME
    if not ENABLE_SERIALIZED_FSN_CSV:
        return
    if (datetime.now() - LAST_SERIALIZED_RELOAD_TIME) > timedelta(hours=INVENTORY_REFRESH_HOURS):
        with serialized_fsn_lock:
            if (datetime.now() - LAST_SERIALIZED_RELOAD_TIME) > timedelta(hours=INVENTORY_REFRESH_HOURS):
                try:
                    sdf = pd.read_csv(SERIALIZED_FSN_CSV_PATH)
                    fsn_col = next((c for c in sdf.columns if 'fsn' in c.lower()), None)
                    vertical_col = next((c for c in sdf.columns if 'vertical' in c.lower()), None)
                    if fsn_col:
                        fsn_series = sdf[fsn_col].dropna().astype(str).str.strip().str.upper()
                        SERIALIZED_FSN_SET = set(fsn_series)
                        if vertical_col:
                            vertical_series = sdf.loc[fsn_series.index, vertical_col].astype(str).str.strip().str.upper()
                            SERIALIZED_FSN_VERTICAL_MAP = dict(zip(fsn_series, vertical_series))
                        else:
                            SERIALIZED_FSN_VERTICAL_MAP = {}
                    LAST_SERIALIZED_RELOAD_TIME = datetime.now()
                    print(f"Loaded serialized_fsn.csv with {len(SERIALIZED_FSN_SET)} FSNs.")
                except FileNotFoundError:
                    SERIALIZED_FSN_SET = set()
                    SERIALIZED_FSN_VERTICAL_MAP = {}
                except Exception as e:
                    print(f"Error loading serialized_fsn.csv: {e}")

def is_serialized_fsn(fsn):
    """True if this FSN requires WSN/IMEI1/IMEI2 capture before it can be logged."""
    fsn_u = str(fsn).strip().upper()
    if not fsn_u or fsn_u in ("N/A", "NAN"):
        return False
    if ENABLE_SERIALIZED_FSN_CSV:
        load_serialized_fsns()
        return fsn_u in SERIALIZED_FSN_SET
    return any(fsn_u.startswith(p.upper()) for p in SERIALIZED_FSN_PREFIXES)

def is_mobile_fsn(fsn):
    """Mobile vs other vertical. When driven by serialized_fsn.csv, the Vertical column
    is authoritative (prefixes alone aren't a reliable way to know a product's vertical
    from that file); falls back to the prefix check if the FSN has no Vertical entry."""
    fsn_u = str(fsn).strip().upper()
    if ENABLE_SERIALIZED_FSN_CSV:
        load_serialized_fsns()
        vertical = SERIALIZED_FSN_VERTICAL_MAP.get(fsn_u)
        if vertical is not None:
            return vertical == MOBILE_VERTICAL_CODE.upper()
    return fsn_u.startswith(MOBILE_FSN_PREFIX.upper())

def is_valid_imei(value):
    """Standard GSMA IMEI validity check: exactly 15 digits, passing the Luhn checksum.
    NOTE: PCR.py (the reference file provided) contains no IMEI-validation logic of its
    own - it's a separate WSN-replacement tool that stores IMEI1/IMEI2 as opaque strings
    and only checks DB uniqueness. This implements the standard algorithm instead."""
    digits = str(value).strip()
    if not digits.isdigit() or len(digits) != 15:
        return False
    total = 0
    for i, ch in enumerate(digits):
        d = int(ch)
        if i % 2 == 1:   # every second digit (0-indexed) is doubled, Luhn-style
            d *= 2
            if d > 9:
                d -= 9
        total += d
    return total % 10 == 0


# Observed WSN format (24VAR7_X, 24VI2Z_R, 24VGNJ_T, 24VH7I_F, 24VGNH_V): 8 characters
# total with "_" as the 7th character. Kept loose (just position, not fixed digit/letter
# slots) since the earlier stricter guess was rejecting valid WSNs.
WSN_FORMAT_RE = re.compile(r'^[A-Z0-9]{6}_[A-Z0-9]$')

def is_valid_wsn_format(wsn):
    """Cheap local check before ever hitting the backend - rejects obviously-wrong
    scans (wrong barcode, fat-fingered EAN, etc.) without spending a network round
    trip on them."""
    return bool(WSN_FORMAT_RE.match(str(wsn).strip().upper()))


# --- flo-lite direct API (view-box, hl_box_audit) ---
# Ported from PackTrack's build_flolite_api_session/api_get_container_details - same
# gateway PackTrack already talks to for its own container/details calls. UNLIKE the
# WSN case, this is flo-lite's real JSON API gateway (needs the x_* headers + CSRF
# token below), not a plain server-rendered page.
# CAVEAT: field names (fsn/product_title/quantity/eans/wid) and the required
# use_case_context=VIEW_BOX_PAGE param are carried over from PackTrack's confirmed
# live capture for its facility - not independently re-verified against every
# warehouse here. That's why scan_box below falls back to the existing Selenium
# scrape if this returns nothing usable, rather than hard-failing the audit.
FLOLITE_URL = "http://10.24.1.71"
PSD_PROXY = f"{FLOLITE_URL}/flo-lite-routes-api/psd-controller-routes/api/v1"
FLOLITE_TENANT_ID = "FKI"
FLOLITE_PSD_TENANT_ID = "Ekart_FK"

def _build_flolite_api_session(driver, facility_id):
    """Cookie+header session for flo-lite's API gateway. Grabs cookies from tab 1
    (always the flo-lite tab on an NCOB pool driver) - no navigation needed, it's
    already there. Mirrors PackTrack's build_flolite_api_session()."""
    handles = driver.window_handles
    original = driver.current_window_handle
    try:
        driver.switch_to.window(handles[1] if len(handles) > 1 else handles[0])
        cookies = driver.get_cookies()
        page = driver.page_source
    finally:
        try: driver.switch_to.window(original)
        except Exception: pass

    csrf_match = re.search(r'<meta name="csrf-token" content="([^"]+)"', page)
    csrf_token = csrf_match.group(1) if csrf_match else None

    user_id = session.get('ldap_id', 'qpex')
    session_cookie = next((c["value"] for c in cookies if c["name"] == "session"), None)
    if session_cookie:
        try:
            data = json.loads(base64.urlsafe_b64decode(session_cookie + "==="))
            flo = data.get("flo-lite", {})
            user_id = flo.get("user", {}).get("userId") or user_id
            facility_id = flo.get("selectedFacilityId") or facility_id
        except Exception:
            pass

    s = requests.Session()
    for c in cookies:
        s.cookies.set(c["name"], c["value"], domain=c.get("domain"), path=c.get("path", "/"))

    user_agent = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                  "(KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36")
    headers = {
        "Accept": "*/*",
        "content-type": "application/json",
        "x_facility_id": facility_id, "X-FACILITY-ID": facility_id,
        "x_requested_by": user_id, "X-REQUESTED-BY": user_id, "X-USER-ID": user_id,
        "x_tenant_id": FLOLITE_TENANT_ID, "X-TENANT-ID": FLOLITE_PSD_TENANT_ID,
        "x_client_id": "WH", "X-CLIENT-ID": "WH",
        "x_process_id": "UI", "X-PROCESS-ID": "UI",
        "Referer": f"{FLOLITE_URL}/flo-lite/{facility_id}/v2/ncob/packing/scan/view-box",
        "x-user-agent": f"{user_agent} EKCL/website/1",
    }
    if csrf_token:
        headers["csrf-token"] = csrf_token
    s.headers.update(headers)
    return s

def api_get_container_details(driver, box_id, facility_id, timeout=15):
    """GET /psd-controller-routes/api/v1/container/{id}/details?use_case_context=VIEW_BOX_PAGE
    Returns the box's item list, or None on any failure (caller falls back to Selenium)."""
    try:
        api = _build_flolite_api_session(driver, facility_id)
        resp = api.get(f"{PSD_PROXY}/container/{box_id}/details", params={"use_case_context": "VIEW_BOX_PAGE"}, timeout=timeout)
        if resp.status_code == 200:
            return resp.json()
    except Exception:
        pass
    return None


# Confirmed via live capture: submitting a WSN on the get_wsn_location page actually
# resolves to this GET with query params - a plain server-rendered HTML page (not a
# flo-lite-style JSON API), so we fetch it with `requests` (cookies borrowed from the
# NCOB pool driver's already-logged-in tab) and parse the returned HTML directly -
# no browser tab/page-load needed per lookup at all.
WSN_LOCATION_PAGE_URL = "http://10.24.1.53/returns/get_wsn_location"
WSN_LOCATION_SEARCH_URL = "http://10.24.1.53/inventory/get_location"
WSN_LOCATION_SEARCH_PARAM = "display_id"
# "Wait until success" per requirement: retries rather than letting an unverified scan
# through. These retries are now cheap plain HTTP calls (no Selenium), so attempts can
# be more frequent than the old tab-scraping version.
WSN_VERIFY_MAX_ATTEMPTS = 3
WSN_VERIFY_RETRY_DELAY_SEC = 2
# WSN is verified as soon as it's scanned (before IMEI is even asked for), then the
# result is cached per-user so the final /scan_product submit reuses it instead of
# re-fetching - the actual save should be instant, not another round trip.
WSN_CACHE_TTL_SEC = 600

# --- Feature toggle: WSN/IMEI backend verification ---
# True (default): every serialized-product scan is verified against get_wsn_location
# (WSN existence + Title/Serial cross-check against IMEI1/IMEI2) before being
# accepted; a mismatch is rejected and logged separately (Result=REJECTED).
# False: WSN is still format-checked locally (cheap, no network) and IMEI1/IMEI2 are
# still captured, but the backend network round-trip and mismatch rejection are
# skipped entirely - reverts to the original pre-verification behavior ("not
# verified against anything yet - just captured and logged").
VERIFY_WSN_SRNO = True

def load_audit_rules():
    global AUDIT_RULES
    try:
        audit_list_path = os.path.join(BASE_DIR, 'Audit_List.csv')
        if os.path.exists(audit_list_path):
            df_rules = pd.read_csv(audit_list_path)
            if 'ShrinkWrap_Audit' in df_rules.columns:
                AUDIT_RULES['shrink_wrap'] = set(df_rules['ShrinkWrap_Audit'].dropna().iloc[1:].astype(str).str.strip().str.lower())
            if 'TamperSeal_Audit' in df_rules.columns:
                AUDIT_RULES['tamper_seal'] = set(df_rules['TamperSeal_Audit'].dropna().iloc[1:].astype(str).str.strip().str.lower())
    except Exception as e:
        print(f"Error loading Audit_List.csv: {e}")

# --- UNIFIED DATABASE SETUP ---
def init_db():
    with db_lock:
        conn = sqlite3.connect(DATABASE_NAME, timeout=60.0)
        cursor = conn.cursor()
        cursor.execute('''
        CREATE TABLE IF NOT EXISTS master_audit_log (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            "Timestamp" TEXT,
            "LDAP ID" TEXT,
            "Warehouse" TEXT,
            "Audit Category" TEXT,
            "Box/Tote ID" TEXT,
            "FSN" TEXT,
            "Product" TEXT,
            "Status" TEXT,
            "Scanned Qty" INTEGER,
            "Expected Qty" INTEGER
        );
        ''')
        
        columns_to_add = {
            "Damage Qty": "TEXT",
            "Expired Qty": "TEXT",
            "Bin Status": "TEXT",
            "TID": "TEXT",
            "Packing SKU": "TEXT",
            "Vertical": "TEXT",
            "Pass_Fail": "TEXT",
            "WID": "TEXT",
            "Scanned IMEI": "TEXT",
            "Order ID": "TEXT",
            "Linked Tracking": "TEXT",
            "Audit No": "TEXT",
            "Image File": "TEXT",
            "WSN": "TEXT",
            "IMEI 2": "TEXT",
            "Rev ID": "TEXT",
            "Issue": "TEXT",
            "Sub Issue": "TEXT",
            "Return Reason": "TEXT",
            "PV Status": "TEXT"
        }
        for col_name, col_type in columns_to_add.items():
            try: cursor.execute(f'ALTER TABLE master_audit_log ADD COLUMN "{col_name}" {col_type}')
            except sqlite3.OperationalError: pass
            
        conn.commit()
        conn.close()

def get_db_connection():
    # Enabled WAL mode for drastically improved concurrency
    conn = sqlite3.connect(DATABASE_NAME, timeout=60.0)
    conn.row_factory = sqlite3.Row
    conn.execute('PRAGMA journal_mode=WAL;') 
    return conn

# --- WAREHOUSE LIST LOADING ---
WH_MAPPING = {}
try:
    wh_list_path = os.path.join(BASE_DIR, 'WH_List.csv')
    wh_df = pd.read_csv(wh_list_path)
    if 'warehouse_name_flolite' in wh_df.columns and 'warehouse_name_flo' in wh_df.columns:
        for _, row in wh_df.iterrows(): 
            WH_MAPPING[str(row['warehouse_name_flo']).strip()] = str(row['warehouse_name_flolite']).strip()
    WAREHOUSES = list(WH_MAPPING.keys())
except Exception as e:
    print(f"Error loading WH_List.csv: {e}")
    WAREHOUSES = []

# --- SELENIUM SESSION MANAGEMENT ---
def create_new_driver(ldap_id, password, warehouse_flo, warehouse_flolite, is_recovery=False):
    options = Options()
    options.add_argument("--disable-gpu")
    options.add_experimental_option("detach", True)
    try:
        driver = webdriver.Chrome(options=options)
        
        driver.get("http://10.24.1.53/")
        time.sleep(2)
        driver.find_element(By.XPATH, "/html/body/div[2]/div[2]/div/div/form/div/div[4]/input[1]").send_keys(ldap_id)
        driver.find_element(By.XPATH, "/html/body/div[2]/div[2]/div/div/form/div/div[4]/input[2]").send_keys(password + Keys.RETURN)
        time.sleep(2)
        
        try:
            wh_dropdown = driver.find_element(By.XPATH, "/html/body/div[3]/div[1]/div[2]/div[1]/div/div[2]/select")
            Select(wh_dropdown).select_by_visible_text(warehouse_flo)
            flo_login_success = True
        except NoSuchElementException:
            flo_login_success = False

        if flo_login_success:
            try:
                driver.execute_script("window.open('http://10.24.1.71/flo-lite', '_blank');")
                driver.switch_to.window(driver.window_handles[1])
                wait = WebDriverWait(driver, 10)
                
                user_input = wait.until(EC.presence_of_element_located((By.XPATH, "/html/body/div[2]/div[2]/div/div/form/div/div[4]/input[1]")))
                user_input.send_keys(ldap_id)
                driver.find_element(By.XPATH, "/html/body/div[2]/div[2]/div/div/form/div/div[4]/input[2]").send_keys(password + Keys.RETURN)
                time.sleep(2)
                
                try: wait.until(EC.invisibility_of_element_located((By.CLASS_NAME, "ModalComponent-overlay-2mpfECNjJxP15VZVFLc1TZ")))
                except TimeoutException: pass
                
                target_btn = wait.until(EC.element_to_be_clickable((By.XPATH, "/html/body/div[1]/div/div/div/div[2]/div/ul/li[2]")))
                driver.execute_script("arguments[0].click();", target_btn)
            except Exception: pass
            finally: driver.switch_to.window(driver.window_handles[0])
            return driver
        else:
            if is_recovery:
                driver.quit()
                return None
            return driver
    except Exception as e:
        print(f"Exception creating driver: {e}")
        if 'driver' in locals() and driver: driver.quit()
        return None

# --- NCOB SHARED SCRAPER POOL ---
ncob_pool = []            # list of {"driver":, "ldap_id":, "lock": Lock()}
ncob_pool_lock = Lock()
NCOB_POOL_DATE = None

def _reset_ncob_pool_if_new_day():
    """Pool membership resets daily - yesterday's 3 auditors shouldn't stay pinned as
    today's shared workers indefinitely."""
    global NCOB_POOL_DATE, ncob_pool
    today = datetime.now().date()
    if NCOB_POOL_DATE != today:
        with ncob_pool_lock:
            if NCOB_POOL_DATE != today:
                for member in ncob_pool:
                    try: member["driver"].quit()
                    except Exception: pass
                ncob_pool = []
                NCOB_POOL_DATE = today

def try_join_ncob_pool(driver, ldap_id):
    """Call right after a successful login. Returns (in_pool, driver_to_keep).
    - Already a member today and their slot is still healthy (e.g. re-login without a
      crash): keeps the existing pool worker driver; caller should quit the
      newly-created `driver`, it's redundant.
    - Already a member but their old slot's driver crashed: the fresh `driver` from
      this login replaces it, so the pool stays at NCOB_POOL_SIZE healthy workers.
    - A free slot exists: this driver becomes a new pool worker.
    - Pool is full: returns (False, driver) - caller should quit `driver`, no personal
      session is needed since NCOB scans will use the shared pool."""
    _reset_ncob_pool_if_new_day()
    with ncob_pool_lock:
        for m in ncob_pool:
            if m["ldap_id"] == ldap_id:
                try:
                    _ = m["driver"].window_handles
                    return True, m["driver"]
                except Exception:
                    try: m["driver"].quit()
                    except Exception: pass
                    m["driver"] = driver
                    return True, driver
        if len(ncob_pool) < NCOB_POOL_SIZE:
            ncob_pool.append({"driver": driver, "ldap_id": ldap_id, "lock": Lock()})
            return True, driver
    return False, driver

def acquire_ncob_pool_driver(timeout=30):
    """Blocks briefly for a free pool worker. Returns the member dict (its lock held)
    or None on timeout - caller MUST call release_ncob_pool_driver() when done."""
    _reset_ncob_pool_if_new_day()
    deadline = time.time() + timeout
    while True:
        with ncob_pool_lock:
            members = list(ncob_pool)
        for member in members:
            if member["lock"].acquire(blocking=False):
                try:
                    _ = member["driver"].window_handles  # health check
                except Exception:
                    member["lock"].release()
                    # Dead worker - evict it now rather than waiting for its owner's
                    # next request, so the pool doesn't quietly shrink below 3 for the
                    # rest of the day. The next successful login claims this slot.
                    with ncob_pool_lock:
                        try: ncob_pool.remove(member)
                        except ValueError: pass
                    continue
                return member
        if time.time() >= deadline:
            return None
        time.sleep(0.2)

def release_ncob_pool_driver(member):
    try: member["lock"].release()
    except Exception: pass

def leave_ncob_pool(ldap_id):
    """Frees this ldap_id's pool slot (if any) and quits its driver, so the next
    successful login can claim the slot - keeps the pool topped up at NCOB_POOL_SIZE
    instead of permanently shrinking after a logout, timeout, or crash."""
    removed = None
    with ncob_pool_lock:
        for i, m in enumerate(ncob_pool):
            if m["ldap_id"] == ldap_id:
                removed = ncob_pool.pop(i)
                break
    if removed:
        try: removed["driver"].quit()
        except Exception: pass

NCOB_SNAPSHOT_CSV_FILENAME = "ncob_box_snapshots.csv"
NCOB_SNAPSHOT_MAX_AGE_HOURS = 24
NCOB_SNAPSHOT_CLEANUP_INTERVAL_HOURS = 12

def _build_flo_api_session(driver):
    """Cookie-only requests.Session for the legacy FLO portal (10.24.1.53). Unlike
    build_flolite_api_session() (flo-lite's API gateway, which needs x_* headers + a
    CSRF token for its JSON endpoints), these are plain server-rendered pages behind
    normal cookie auth - copying the login cookies over is enough for a GET lookup.
    Briefly switches to tab 0 (always the FLO/10.24.1.53 tab for pool drivers) to read
    them, then switches back - no page navigation needed since it's already there."""
    handles = driver.window_handles
    original = driver.current_window_handle
    try:
        driver.switch_to.window(handles[0])
        cookies = driver.get_cookies()
    finally:
        try: driver.switch_to.window(original)
        except Exception: pass

    s = requests.Session()
    for c in cookies:
        s.cookies.set(c["name"], c["value"], domain=c.get("domain"), path=c.get("path", "/"))
    s.headers.update({
        "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                        "(KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36"),
        "Referer": WSN_LOCATION_PAGE_URL,
    })
    return s


def _parse_wsn_location_html(html_text):
    """Same label-matched extraction as the old Selenium version (any <table><tr> with
    >=2 cells, first cell = label, second = value) - just against a fetched HTML
    string via lxml/xpath instead of a live DOM. Also captures the site's own inline
    error message (invalid/unknown WSN etc.) when no results table is present, and
    strips the site's literal leading "'" text-forcing artifact from values."""
    try:
        tree = lxml_html.fromstring(html_text)
    except Exception:
        return {"found": False, "error_message": ""}

    label_map = {}
    for row in tree.xpath("//table//tr"):
        cells = row.xpath("./td")
        if len(cells) >= 2:
            label = cells[0].text_content().strip()
            value = cells[1].text_content().strip().lstrip("'")
            if label:
                label_map[label] = value

    if label_map:
        return {
            "found": True,
            "title": label_map.get("Title", ""),
            "serial": label_map.get("Return Serial Numbers", ""),
            "rev_id": label_map.get("Return Shipment Id", ""),
            "fsn": label_map.get("FSN", ""),
            "vertical": label_map.get("Vertical", ""),
        }

    for err_xp in ["/html/body/div[3]/div[1]/div[5]", "/html/body/div[3]/div/div[5]"]:
        err_elems = tree.xpath(err_xp)
        if err_elems:
            err_text = err_elems[0].text_content().strip()
            if err_text:
                return {"found": False, "error_message": err_text}

    return {"found": False, "error_message": ""}


def _fetch_wsn_location(driver, wsn):
    """GET the confirmed search URL directly - no browser tab/page-load per lookup."""
    api = _build_flo_api_session(driver)
    resp = api.get(WSN_LOCATION_SEARCH_URL, params={WSN_LOCATION_SEARCH_PARAM: wsn, "searchbtn": "Search"}, timeout=10)
    if resp.status_code != 200:
        return {"found": False, "error_message": f"HTTP {resp.status_code} from get_location."}
    return _parse_wsn_location_html(resp.text)


def verify_wsn_with_backend(wsn):
    """Looks up `wsn` via a direct HTTP GET (cookies borrowed from a free NCOB pool
    worker's tab, then released immediately - the network request itself never holds
    up the shared Selenium pool). Per requirement, the auditor waits rather than the
    scan going through unverified: retries until a result comes back, INCLUDING if all
    3 pool workers are busy (that's retried too, not just the HTTP call - a single busy
    window no longer fails the whole lookup). Raises RuntimeError once
    WSN_VERIFY_MAX_ATTEMPTS is exhausted - caller must surface that as a retry-able
    error, never silently accept the scan."""
    if not is_valid_wsn_format(wsn):
        raise RuntimeError(f"'{wsn}' is not a valid WSN format (expected 8 chars, e.g. 24VAR7_X).")

    api = None
    last_err = "unknown error"
    for _ in range(WSN_VERIFY_MAX_ATTEMPTS):
        if api is None:
            pool_member = acquire_ncob_pool_driver(timeout=15)
            if not pool_member:
                last_err = "All 3 NCOB scraper sessions are busy."
                time.sleep(WSN_VERIFY_RETRY_DELAY_SEC)
                continue
            try:
                api = _build_flo_api_session(pool_member["driver"])
            except Exception as e:
                last_err = f"Could not read login session: {e}"
                release_ncob_pool_driver(pool_member)
                time.sleep(WSN_VERIFY_RETRY_DELAY_SEC)
                continue
            release_ncob_pool_driver(pool_member)

        try:
            resp = api.get(WSN_LOCATION_SEARCH_URL, params={WSN_LOCATION_SEARCH_PARAM: wsn, "searchbtn": "Search"}, timeout=10)
            if resp.status_code == 200:
                result = _parse_wsn_location_html(resp.text)
                if result.get("found"):
                    return result
                last_err = result.get("error_message") or "WSN not found on get_wsn_location."
            elif resp.status_code in (401, 403):
                last_err = f"HTTP {resp.status_code} (login session may have expired)."
                api = None   # force grabbing fresh cookies next attempt
            else:
                last_err = f"HTTP {resp.status_code} from get_location."
        except Exception as e:
            last_err = str(e)
        time.sleep(WSN_VERIFY_RETRY_DELAY_SEC)
    raise RuntimeError(f"WSN verification failed after {WSN_VERIFY_MAX_ATTEMPTS} attempts: {last_err}")



def log_ncob_snapshot(box_id, extracted_data, pool_ldap_id, auditor_ldap_id):
    """Dedicated audit-trail CSV of exactly what the pool scraped for this box, kept
    separate from the eventual audit result. Always logged under the requesting
    auditor's own LDAP ID - the pool worker's identity is recorded too, but only for
    our own traceability of which shared session did the scraping. A box is always
    re-scraped fresh on every scan, so any previous snapshot rows for this same
    box_id are dropped first - the CSV keeps only the latest snapshot per box,
    not a growing pile of stale re-scans."""
    timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    new_rows = [{
        "Timestamp": timestamp,
        "Box/Tote ID": box_id,
        "Auditor": auditor_ldap_id,
        "Pool Worker": pool_ldap_id,
        "FSN": item.get("FSN", "N/A"),
        "Product": item.get("Product", ""),
        "Qty": item.get("Qty", ""),
        "WID": item.get("WID", "N/A")
    } for item in extracted_data]

    path = os.path.join(CSV_DIR, NCOB_SNAPSHOT_CSV_FILENAME)
    with csv_lock:
        try:
            existing = pd.read_csv(path) if os.path.exists(path) else pd.DataFrame()
        except Exception as e:
            print(f"Error reading {NCOB_SNAPSHOT_CSV_FILENAME} before rewrite: {e}")
            existing = pd.DataFrame()

        if not existing.empty and "Box/Tote ID" in existing.columns:
            existing = existing[existing["Box/Tote ID"].astype(str).str.strip().str.upper() != str(box_id).strip().upper()]

        combined = pd.concat([existing, pd.DataFrame(new_rows)], ignore_index=True) if not existing.empty else pd.DataFrame(new_rows)
        try:
            combined.to_csv(path, index=False)
        except Exception as e:
            print(f"Error writing {NCOB_SNAPSHOT_CSV_FILENAME}: {e}")

def cleanup_ncob_snapshots():
    """Drops rows from ncob_box_snapshots.csv whose Timestamp is
    NCOB_SNAPSHOT_MAX_AGE_HOURS (24h) old or older. Runs on its own timer, independent
    of any request, so the file doesn't grow unbounded."""
    path = os.path.join(CSV_DIR, NCOB_SNAPSHOT_CSV_FILENAME)
    with csv_lock:
        if not os.path.exists(path):
            return
        try:
            df = pd.read_csv(path)
            if df.empty or "Timestamp" not in df.columns:
                return
            ts = pd.to_datetime(df["Timestamp"], errors="coerce")
            cutoff = datetime.now() - timedelta(hours=NCOB_SNAPSHOT_MAX_AGE_HOURS)
            # Rows with an unparseable timestamp are kept rather than silently dropped.
            kept = df[ts.isna() | (ts >= cutoff)]
            dropped = len(df) - len(kept)
            if dropped > 0:
                kept.to_csv(path, index=False)
                print(f"ncob_box_snapshots.csv cleanup: dropped {dropped} row(s) >= {NCOB_SNAPSHOT_MAX_AGE_HOURS}h old.")
        except Exception as e:
            print(f"Error cleaning {NCOB_SNAPSHOT_CSV_FILENAME}: {e}")

def ncob_snapshot_cleaner():
    """Background loop: cleans immediately on startup (in case old rows piled up while
    the app was down), then every NCOB_SNAPSHOT_CLEANUP_INTERVAL_HOURS (12h) after."""
    while True:
        cleanup_ncob_snapshots()
        time.sleep(NCOB_SNAPSHOT_CLEANUP_INTERVAL_HOURS * 3600)

def get_user_context():
    with sessions_lock:
        user_id = session.get('user_id')
        
        if not user_id:
            session.clear()
            return None

        if user_id not in user_sessions:
            # The server doesn't know this session anymore - either it restarted (wiping
            # user_sessions and the NCOB pool) or this session was reaped for inactivity.
            # Don't silently replay cached credentials from the cookie to spin up a new
            # driver behind the scenes: that bypasses try_join_ncob_pool() entirely, which
            # is exactly how the pool was ending up permanently empty after a restart.
            # Force a real relogin through /login instead.
            session.clear()
            return None

        try:
            drv = user_sessions[user_id].get("driver")
            if drv is None:
                raise RuntimeError("no personal driver (deferred)")
            _ = drv.window_handles
        except Exception:
            # Users who logged in after the daily NCOB pool of 3 filled up are given no
            # personal driver at login (personal_driver_deferred=True) - don't eagerly
            # recreate one here on every request. ensure_personal_driver() creates it
            # lazily, only if/when they actually pick a non-NCOB audit type.
            if user_sessions[user_id].get("personal_driver_deferred"):
                pass
            else:
                # Their personal driver crashed. Don't silently reconnect behind their
                # back - clear the session and free their NCOB pool slot (if any) so
                # they have to log back in cleanly.
                ldap_id = user_sessions[user_id].get("ldap_id")
                del user_sessions[user_id]
                session.clear()
                if ldap_id:
                    leave_ncob_pool(ldap_id)
                return None

        user_sessions[user_id]["last_seen"] = datetime.now()
        return user_sessions[user_id]

def ensure_personal_driver(context):
    """Lazily creates/heals a personal Selenium session for non-NCOB audit types only.
    No-op if a healthy driver already exists. Auditors who only ever do NCOB Box Audit
    (serviced entirely by the shared pool) never end up needing one. If a driver
    existed and crashed, the user is logged out and must sign back in - no silent
    auto-reconnect."""
    driver = context.get("driver")
    if driver is not None:
        try:
            _ = driver.window_handles
            return driver
        except Exception:
            user_id = session.get('user_id')
            ldap_id = context.get("ldap_id")
            with sessions_lock:
                if user_id and user_id in user_sessions:
                    try: user_sessions[user_id]["driver"].quit()
                    except Exception: pass
                    del user_sessions[user_id]
            if ldap_id:
                leave_ncob_pool(ldap_id)
            session.clear()
            return None

    # No personal driver yet (first time this user needs one) - create it fresh.
    warehouse_flolite = session.get('warehouse_flolite') or WH_MAPPING.get(session.get('warehouse_id'))
    if not warehouse_flolite:
        return None
    new_driver = create_new_driver(session.get('ldap_id'), session.get('password'), session.get('warehouse_id'), warehouse_flolite, is_recovery=True)
    if not new_driver:
        return None
    context["driver"] = new_driver
    context["personal_driver_deferred"] = False
    return new_driver


# --- Helper: Consolidate Audits (Crucial for Multi-Part OB Orders) ---
def consolidate_ob_audits(df):
    if df.empty: return df
    
    if 'Order ID' in df.columns:
        df['Order ID'] = df['Order ID'].fillna('N/A')
        df['Box/Tote ID'] = df['Box/Tote ID'].fillna('N/A')
        
        df['Group_Key'] = df.apply(lambda x: str(x['Order ID']) if str(x['Order ID']).strip() != 'N/A' else str(x['Box/Tote ID']), axis=1)
        
        df = df.sort_values('Timestamp', ascending=False)
        
        agg_funcs = {}
        for col in df.columns:
            if col in ['Group_Key', 'FSN', 'WID', 'Product']: continue
            elif col == 'Box/Tote ID': agg_funcs[col] = lambda x: ' | '.join(sorted(set(str(v) for v in x.dropna() if str(v)!='N/A')))
            elif col == 'Linked Tracking': agg_funcs[col] = lambda x: ' | '.join(sorted(set(str(v) for v in x.dropna() if str(v)!='N/A')))
            elif col in ['Expected Qty', 'Scanned Qty']: agg_funcs[col] = 'max'
            elif col == 'Status': agg_funcs[col] = lambda x: x.iloc[0]
            elif col == 'Scanned IMEI': agg_funcs[col] = lambda x: next((str(v) for v in x if pd.notna(v) and str(v).strip()), "")
            else: agg_funcs[col] = 'first'
            
        grouped = df.groupby(['Group_Key', 'FSN', 'WID', 'Product'], as_index=False).agg(agg_funcs)
        
        def recalc_status(row):
            orig = str(row['Status']).upper()
            if 'ALIEN' in orig or 'MISSHIP' in orig: return orig
            
            sq = pd.to_numeric(row['Scanned Qty'], errors='coerce')
            eq = pd.to_numeric(row['Expected Qty'], errors='coerce')
            if pd.isna(sq): sq = 0
            if pd.isna(eq): eq = 0
            
            st = "OK"
            if sq == eq: st = "OK"
            elif sq > eq: st = "EXCESS"
            else:
                st = "SHORT"
                if 'Unscanned' in orig: st = "Unscanned Part"
                
            if 'IMEI Mismatch' in orig: st += " (IMEI Mismatch)"
            return st
            
        grouped['Status'] = grouped.apply(recalc_status, axis=1)
        grouped = grouped.drop(columns=['Group_Key'])
        grouped = grouped.sort_values('Timestamp', ascending=False)
        return grouped
    return df

# --- Helper: CQ Report Generator ---
def generate_cq_report(df):
    cq_rows = []

    # NCOB/OB Audit rows are stored one-row-per-FSN-per-box in master_audit_log, but
    # the reference OB Audit export is one-row-per-box (confirmed: 311 rows for 311
    # distinct totes, no duplicates). Aggregate every FSN row for the same box+audit
    # instance into a single box-level summary row here, before the per-row loop below
    # (which still handles Bin Audit / fallback categories exactly as before).
    df = df.copy()
    cat_upper = df.get('Audit Category', '').astype(str).str.upper()
    is_ob_mask = cat_upper.apply(lambda c: 'NCOB BOX AUDIT' in c or 'OUTBOUND AUDIT' in c or c in ['HL_BOX_AUDIT', 'OB_AUDIT'])
    ob_df = df[is_ob_mask]
    other_df = df[~is_ob_mask]

    if not ob_df.empty:
        group_cols = ['Box/Tote ID', 'Audit No'] if 'Audit No' in ob_df.columns else ['Box/Tote ID']
        for _, box_rows in ob_df.groupby(group_cols, dropna=False):
            first = box_rows.iloc[0]
            box_id = first.get('Box/Tote ID', '')
            ldap_id = first.get('LDAP ID', '')

            units_studied = 0
            units_failed = 0
            issue_hits = []   # (priority rank, Issue label, Remarks label) - one per FSN with an issue

            for _, row in box_rows.iterrows():
                sq = pd.to_numeric(row.get('Scanned Qty', 0), errors='coerce')
                eq = pd.to_numeric(row.get('Expected Qty', 0), errors='coerce')
                if pd.isna(sq): sq = 0
                if pd.isna(eq): eq = 0
                dq = pd.to_numeric(row.get('Damage Qty', 0), errors='coerce')
                if pd.isna(dq): dq = 0

                units_studied += max(sq, eq)

                status_upper = str(row.get('Status', '')).upper()
                if 'MISSHIP' in status_upper or 'ALIEN' in status_upper:
                    units_failed += max(sq, eq)
                    issue_hits.append((0, "Misshipment", "Misshipment"))
                elif 'SHORT' in status_upper or 'UNSCANNED' in status_upper:
                    units_failed += abs(sq - eq)
                    issue_hits.append((1, "Missing", "Short"))
                elif 'EXCESS' in status_upper:
                    units_failed += abs(sq - eq)
                    issue_hits.append((2, "Excess", "Excess"))
                elif dq > 0:
                    units_failed += dq
                    issue_hits.append((3, "Damage", "Damaged"))

            # A box can have several FSNs with different issues - report the most
            # severe one at box level (Misshipment > Missing > Excess > Damage), same
            # rule as the per-FSN issue-mapping (Alien/Misship->Misshipment,
            # Short->Missing, Excess->Excess).
            if issue_hits:
                issue_hits.sort(key=lambda x: x[0])
                issue_val, remarks_val = issue_hits[0][1], issue_hits[0][2]
                failed = 1
            else:
                issue_val, remarks_val, failed = "No Issue", "No Issue", 0

            image_file = str(first.get('Image File', ''))
            if pd.isna(image_file) or str(image_file).strip() == 'None':
                image_file = ""
            final_remarks = image_file if image_file else remarks_val

            cq_rows.append({
                "Quality Gate No": "",
                "Quality gate type": "OB Audit",
                "Tracking ID/Tote ID": box_id,
                "Audit Location": "Staging Area",
                "SM/GTNL/Stack Merge": "",
                "Product Placed As per Volumetric?": "Yes",
                "Tote Size": "",
                "Issue": issue_val,
                "Samples Studied": 1,
                "Samples Failed": failed,
                "Tote Utilization %": "",
                "Able to fit in Small Tote?": "",
                "Auditee Contact/Ops POC": "",
                "Units Studied": int(units_studied),
                "Units Failed": int(units_failed),
                "Remarks": final_remarks,
                "Actual Product FSN/Actual Loc id/Bin Id": ""
            })

    for _, row in other_df.iterrows():
        cat = str(row.get('Audit Category', '')).upper()
        timestamp_val = str(row.get('Timestamp', ''))
        
        date_str = ""
        if timestamp_val and timestamp_val != 'None':
            try:
                date_str = datetime.strptime(timestamp_val, '%Y-%m-%d %H:%M:%S').strftime('%m/%d/%Y')
            except:
                date_str = timestamp_val[:10]
                
        # 1. BIN AUDIT
        if 'BIN AUDIT' in cat or cat in ['UNIT', 'BULK']:
            box_id = row.get('Box/Tote ID', '')
            wid = row.get('WID', '')
            trigger = row.get('Bin Status', '')
            if pd.isna(trigger) or not trigger or str(trigger).strip() == 'None':
                trigger = 'PST locations'
                
            sq = pd.to_numeric(row.get('Scanned Qty', 0), errors='coerce')
            eq = pd.to_numeric(row.get('Expected Qty', 0), errors='coerce')
            if pd.isna(sq): sq = 0
            if pd.isna(eq): eq = 0
            
            dq = pd.to_numeric(row.get('Damage Qty', 0), errors='coerce')
            exq = pd.to_numeric(row.get('Expired Qty', 0), errors='coerce')
            if pd.isna(dq): dq = 0
            if pd.isna(exq): exq = 0
            
            status = str(row.get('Status', ''))
            image_file = str(row.get('Image File', ''))
            if pd.isna(image_file) or str(image_file).strip() == 'None':
                image_file = ""
                
            samples_studied = max(sq, eq)
            if samples_studied == 0:
                samples_studied = 1
                
            issues_logged = []
            
            # Variance Issue
            if sq != eq:
                sub_issue = "Short Qty" if sq < eq else "Excess Qty"
                impacted = abs(sq - eq)
                issues_logged.append({
                    "Issue": "Variance(Short/Excess)",
                    "Sub Issue": sub_issue,
                    "Impacted": impacted,
                    "Failed": 1
                })
                
            # Damage Issue
            if dq > 0:
                issues_logged.append({
                    "Issue": "Product Damaged",
                    "Sub Issue": "Damaged",
                    "Impacted": int(dq),
                    "Failed": 1
                })
                
            # Expired Issue
            if exq > 0:
                issues_logged.append({
                    "Issue": "Product Expired",
                    "Sub Issue": "Expired",
                    "Impacted": int(exq),
                    "Failed": 1
                })
                
            # Fallback: No Issue
            if not issues_logged:
                issues_logged.append({
                    "Issue": "No Issue",
                    "Sub Issue": "No Issue",
                    "Impacted": 0,
                    "Failed": 0
                })
                
            for issue in issues_logged:
                cq_rows.append({
                    "Quality Gate No": "",
                    "Date": date_str,
                    "Quality Gate type": "Bin",
                    "Trigger": trigger,
                    "Issue": issue["Issue"],
                    "Sub Issue": issue["Sub Issue"],
                    "Master / Super category": "",
                    "Brand": "",
                    "FSN on WID / Consignment ID": wid,
                    "Actual Product FSN/Actual Loc id/Bin Id": box_id,
                    "Impacted/Variance Quantity": issue["Impacted"],
                    "Remarks": "",
                    "Samples Studied": int(samples_studied),
                    "Samples Failed": issue["Failed"],
                    "Original Image Upload": image_file
                })
                
        # 2. Fallback Layout (Covers PV, Proxy Pack, etc. - NCOB/OB Audit rows are
        # handled by the box-level aggregation pass above, before this loop)
        else:
            box_id = row.get('Box/Tote ID', '')
            if not box_id:
                box_id = row.get('WSN', '')
            status_upper = str(row.get('Status', '')).upper()
            image_file = str(row.get('Image File', ''))
            if pd.isna(image_file) or str(image_file).strip() == 'None':
                image_file = ""
                
            failed = 1 if ('SHORT' in status_upper or 'EXCESS' in status_upper or 'MISSHIP' in status_upper or 'ALIEN' in status_upper or 'FAIL' in status_upper) else 0
            issue_val = str(row.get('Status', 'No Issue'))
            
            cq_rows.append({
                "Quality Gate No": "",
                "Date": date_str,
                "Quality Gate type": cat,
                "Trigger": "General Audit",
                "Issue": issue_val,
                "Sub Issue": issue_val,
                "Master / Super category": "",
                "Brand": "",
                "FSN on WID / Consignment ID": row.get('WID', ''),
                "Actual Product FSN/Actual Loc id/Bin Id": box_id,
                "Impacted/Variance Quantity": row.get('Scanned Qty', 0),
                "Remarks": "",
                "Samples Studied": row.get('Expected Qty', 1),
                "Samples Failed": failed,
                "Original Image Upload": image_file
            })
               
    return pd.DataFrame(cq_rows)

# --- FLASK ROUTES ---

@app.route("/", methods=["GET", "POST"])
def login():
    if 'ldap_id' in session and session.get('user_id') in user_sessions:
        return redirect(url_for("landing"))

    try:
        if datetime.now() - datetime.fromtimestamp(os.path.getmtime(INVENTORY_CSV_PATH)) > timedelta(hours=25):
            flash("Inventory File Not Updated - Contact Supervisor", "flash-danger")
            if request.method == "POST": return redirect(url_for("login"))
    except FileNotFoundError:
        flash("CRITICAL: Inventory.csv not found.", "flash-danger")
        if request.method == "POST": return redirect(url_for("login"))

    if request.method == "POST":
        if 'otp_input' in request.form:
            temp_id = request.form.get('temp_id')
            driver = driver_store.get(temp_id)
            if not driver: return redirect(url_for("login"))
            try:
                otp_field = driver.find_element(By.XPATH, "/html/body/div[2]/div[2]/div/div[3]/div[2]/div/div/form/table/tbody/tr[2]/td/table/tbody/tr[3]/td/input")
                otp_field.send_keys(request.form.get('otp_input'))
                driver.find_element(By.XPATH, "/html/body/div[2]/div[2]/div/div[3]/div[2]/div/div/form/table/tbody/tr[2]/td/table/tbody/tr[7]/td/div/button[1]").click()
                wh_element = WebDriverWait(driver, 10).until(EC.visibility_of_element_located((By.XPATH, "/html/body/div[3]/div[1]/div[2]/div[1]/div/div[2]/select")))
                Select(wh_element).select_by_visible_text(session.get('pending_warehouse_id'))
                
                try:
                    driver.execute_script("window.open('http://10.24.1.71/flo-lite', '_blank');")
                    driver.switch_to.window(driver.window_handles[1])
                    wait = WebDriverWait(driver, 10)
                    user_input = wait.until(EC.presence_of_element_located((By.XPATH, "/html/body/div[2]/div[2]/div/div/form/div/div[4]/input[1]")))
                    user_input.send_keys(session.get('ldap_id'))
                    driver.find_element(By.XPATH, "/html/body/div[2]/div[2]/div/div/form/div/div[4]/input[2]").send_keys(session.get('password') + Keys.RETURN)
                    time.sleep(2)
                    try: wait.until(EC.invisibility_of_element_located((By.CLASS_NAME, "ModalComponent-overlay-2mpfECNjJxP15VZVFLc1TZ")))
                    except TimeoutException: pass
                    target_btn = wait.until(EC.element_to_be_clickable((By.XPATH, "/html/body/div[1]/div/div/div/div[2]/div/ul/li[2]")))
                    driver.execute_script("arguments[0].click();", target_btn)
                except Exception: pass
                finally: driver.switch_to.window(driver.window_handles[0])

                session['user_id'] = str(uuid.uuid4())
                session['warehouse_id'] = session.get('pending_warehouse_id')
                
                warehouse_flolite = WH_MAPPING.get(session['warehouse_id'])
                if not warehouse_flolite:
                    driver.quit()
                    flash(f"Error: Flo-Lite configuration missing for warehouse '{session['warehouse_id']}'.", "flash-danger")
                    return redirect(url_for("login"))
                session['warehouse_flolite'] = warehouse_flolite
                
                load_global_inventory()
                in_pool, pool_driver = try_join_ncob_pool(driver, session['ldap_id'])
                if in_pool:
                    if pool_driver is not driver:
                        try: driver.quit()
                        except Exception: pass
                        driver = pool_driver
                    deferred = False
                else:
                    try: driver.quit()
                    except Exception: pass
                    driver = None
                    deferred = True
                user_sessions[session['user_id']] = {
                    "driver": driver, "df": pd.DataFrame(), "scanned_items": {}, "box_id": None, 
                    "scan_history": [], "audit_type": "unit", "last_seen": datetime.now(), "inventory_df": MASTER_INVENTORY_DF.copy(),
                    "personal_driver_deferred": deferred, "ldap_id": session['ldap_id']
                }
                return redirect(url_for("landing"))
            except Exception as e:
                print(f"OTP Submission Exception: {e}")
                driver.quit()
                return redirect(url_for("login"))
                
        else:
            ldap_id, password, warehouse_flo = request.form.get("ldap_id"), request.form.get("password"), request.form.get("warehouse_id")
            
            warehouse_flolite = WH_MAPPING.get(warehouse_flo)
            if not warehouse_flolite:
                flash(f"Configuration Error: Flo-Lite mapping not found for '{warehouse_flo}'. Please check WH_List.csv.", "flash-danger")
                return redirect(url_for("login"))
                
            driver = create_new_driver(ldap_id, password, warehouse_flo, warehouse_flolite)
            if not driver:
                flash("Login failed. Please check your credentials.", "flash-danger")
                return redirect(url_for("login"))

            try:
                driver.find_element(By.XPATH, "/html/body/div[3]/div[1]/div[2]/div[1]/div/div[2]/select")
                session.update({'user_id': str(uuid.uuid4()), 'ldap_id': ldap_id, 'password': password, 'warehouse_id': warehouse_flo, 'warehouse_flolite': warehouse_flolite})
                load_global_inventory()
                in_pool, pool_driver = try_join_ncob_pool(driver, ldap_id)
                if in_pool:
                    if pool_driver is not driver:
                        try: driver.quit()
                        except Exception: pass
                        driver = pool_driver
                    deferred = False
                else:
                    try: driver.quit()
                    except Exception: pass
                    driver = None
                    deferred = True
                user_sessions[session['user_id']] = {
                    "driver": driver, "df": pd.DataFrame(), "scanned_items": {}, "box_id": None,
                    "scan_history": [], "audit_type": "unit", "last_seen": datetime.now(), "inventory_df": MASTER_INVENTORY_DF.copy(),
                    "personal_driver_deferred": deferred, "ldap_id": ldap_id
                }
                return redirect(url_for("landing"))
            except NoSuchElementException:
                try:
                    driver.find_element(By.XPATH, "/html/body/div[2]/div[2]/div/div[3]/div[1]/h4/a").click()
                    time.sleep(1)
                    driver.find_element(By.XPATH, "/html/body/div[2]/div[2]/div/div[3]/div[2]/div/div/form/table/tbody/tr[2]/td/table/tbody/tr[1]/td/div/button/span").click()
                    temp_id = str(uuid.uuid4())
                    driver_store[temp_id] = driver
                    session.update({'ldap_id': ldap_id, 'password': password, 'pending_warehouse_id': warehouse_flo})
                    return render_template("login.html", warehouses=WAREHOUSES, show_otp_popup=True, temp_id=temp_id)
                except Exception:
                    driver.quit()
                    return redirect(url_for("login"))
                    
    return render_template("login.html", warehouses=WAREHOUSES)

@app.route("/landing")
def landing():
    if 'ldap_id' not in session: return redirect(url_for("login"))
    if not get_user_context(): return redirect(url_for("login"))
    return render_template("landing.html")

@app.route("/dashboard")
def dashboard():
    if 'ldap_id' not in session: return redirect(url_for("login"))
    conn = get_db_connection()
    try:
        today = datetime.now().strftime('%Y-%m-%d')
        # Corrected alias column names to align with dashboard.html expectation
        stats = conn.execute('''
            SELECT "Audit Category", "LDAP ID", COUNT(DISTINCT "Audit No") as Boxes_Audited, SUM("Scanned Qty") as Items_Audited 
            FROM master_audit_log 
            WHERE "Timestamp" LIKE ?
            GROUP BY "Audit Category", "LDAP ID"
        ''', (f'{today}%',)).fetchall()
    finally:
        conn.close()
    return render_template("dashboard.html", stats=stats, date=today)

@app.route("/scanner/<audit_type>")
def scanner(audit_type):
    context = get_user_context()
    if not context: return redirect(url_for("login"))
    
    # NCOB Box Audit is serviced by the shared pool inside /scan_box - no personal
    # driver is created here (or at all, for auditors relying purely on the pool).
    driver = ensure_personal_driver(context) if audit_type != 'hl_box_audit' else None
    if audit_type != 'hl_box_audit' and not driver:
        return redirect(url_for("login"))
    url_map = {
        'unit': "http://10.24.1.53/inventory/view_store_inventory",
        'bulk': "http://10.24.1.53/inventory/view_store_inventory",
        'picklist': "http://10.24.1.53/storage_locations/view_tote",
        'putlist': "http://10.24.1.53/inventory/find_putlists",
        'ob_audit': "http://10.24.1.53/shipments/find_shipments",
        'hl_box_audit': f"http://10.24.1.71/flo-lite/{session.get('warehouse_flolite')}/v2/ncob/packing/scan/view-box"
    }
    
    target_url = url_map.get(audit_type)
    if target_url and driver:
        try:
            driver.switch_to.window(driver.window_handles[0])
            driver.get(target_url)
            time.sleep(1)
        except Exception as e:
            print(f"Pre-load URL error: {e}")

    context.update({"audit_type": audit_type, "scanned_items": {}, "df": pd.DataFrame(), "scan_history": []})
    
    ui_config = {
        "unit": {"title": "Bin Audit (Unit)", "placeholder": "Scan Bin Label"},
        "bulk": {"title": "Bin Audit (Bulk)", "placeholder": "Scan Bin Label"},
        "putlist": {"title": "Putlist Audit", "placeholder": "Scan Tote ID"},
        "picklist": {"title": "Picklist Audit", "placeholder": "Scan Tote ID"},
        "ob_audit": {"title": "Customer Outbound Audit", "placeholder": "Scan Tracking ID"},
        "hl_box_audit": {"title": "NCOB Box Audit", "placeholder": "Scan Box/Tote ID"},
        "proxy_pack": {"title": "Proxy Packaging Audit"},
        "shrink_wrap": {"title": "ShrinkWrap Audit"},
        "tamper_seal": {"title": "TamperSeal Audit"},
        "cx_misship": {"title": "PV Audit", "placeholder": "Scan WSN"}
    }
    config = ui_config.get(audit_type, ui_config["unit"])
    
    if audit_type == 'bulk': return render_template("index_bulk.html", config=config)
    elif audit_type == 'proxy_pack': return render_template("audit_proxy.html", config=config)
    elif audit_type in ['shrink_wrap', 'tamper_seal']: return render_template("audit_quality.html", config=config, audit_type=audit_type)
    elif audit_type == 'cx_misship': return render_template("pv_audit.html", config=config)
    else: return render_template("index_unit.html", config=config)

# =========================================================================
# --- API ROUTES (Proxy Pack, ShrinkWrap, TamperSeal) ---
# =========================================================================

@app.route("/api/submit_proxy_pack", methods=["POST"])
def submit_proxy_pack():
    context = get_user_context()
    if not context: return jsonify({"status": "error", "message": "Session expired."}), 401

    tid = request.form.get("tid", "").strip()
    packing_sku = request.form.get("packing_sku", "").strip()

    if not tid or not packing_sku:
        return jsonify({"status": "error", "message": "TID and Packing SKU are required."}), 400

    audit_no = generate_audit_no("proxy", tid)
    evidence_file = request.files.get('evidence_image')
    image_name = save_evidence_image(evidence_file, "proxy_pack", audit_no)

    timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    ldap_id = session.get('ldap_id', 'UNKNOWN')
    warehouse = session.get('warehouse_id', 'UNKNOWN')
    audit_category = "PROXY PACKAGING AUDIT"

    with db_lock:
        conn = get_db_connection()
        try:
            conn.execute('''
                INSERT INTO master_audit_log ("Timestamp", "LDAP ID", "Warehouse", "Audit Category", "Box/Tote ID", "FSN", "WID", "Product", "Status", "Scanned Qty", "Expected Qty", "TID", "Packing SKU", "Audit No", "Image File")
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ''', (timestamp, ldap_id, warehouse, audit_category, tid, "N/A", "N/A", "N/A", "OK", 1, 1, tid, packing_sku, audit_no, image_name))
            conn.commit()
        finally:
            conn.close()

    data = {
        "Timestamp": timestamp, "LDAP ID": ldap_id, "Warehouse": warehouse,
        "Audit Category": audit_category, "Box/Tote ID": tid, "FSN": "N/A",
        "Product": "N/A", "Status": "OK", "Expected Qty": 1, "Scanned Qty": 1, 
        "TID": tid, "Packing SKU": packing_sku,
        "WID": "N/A", "Order ID": "N/A", "Linked Tracking": "N/A",
        "Audit No": audit_no, "Image File": image_name
    }
    safe_csv_export([data], "proxy_pack_audit_NL.csv")

    return jsonify({"status": "success", "message": "Proxy Packaging Audit saved successfully!"})

@app.route("/api/verify_wsn", methods=["POST"])
def api_verify_wsn():
    """Called as soon as a WSN is scanned in the serialized-capture popup (before the
    auditor even gets to type an IMEI). Rejects malformed WSNs locally without a
    network call, then looks the WSN up and caches the result on the user's context so
    the eventual /scan_product submit doesn't have to fetch it again."""
    context = get_user_context()
    if not context:
        return jsonify({"status": "error", "message": "Session expired. Please log in again."}), 401

    wsn = request.form.get("wsn", "").strip()
    if not wsn:
        return jsonify({"status": "error", "message": "WSN required."}), 400

    if not is_valid_wsn_format(wsn):
        return jsonify({"status": "error", "message": f"'{wsn}' doesn't look like a valid WSN (expected format e.g. 24VAR7_X)."})

    if not VERIFY_WSN_SRNO:
        # Verification toggled off - just log it (format-checked, not backend-checked).
        return jsonify({"status": "success", "verified": False, "title": "", "serial": "", "fsn": "", "vertical": ""})

    try:
        result = verify_wsn_with_backend(wsn)
    except RuntimeError as e:
        return jsonify({"status": "error", "message": f"Could not verify WSN ({e}). Please rescan."})

    cache = context.setdefault("wsn_cache", {})
    cache[wsn.upper()] = {"result": result, "ts": datetime.now()}

    return jsonify({
        "status": "success",
        "verified": True,
        "title": result.get("title", ""),
        "serial": result.get("serial", ""),
        "fsn": result.get("fsn", ""),
        "vertical": result.get("vertical", "")
    })

@app.route("/api/check_quality_wid", methods=["POST"])
def check_quality_wid():
    context = get_user_context()
    if not context: return jsonify({"status": "error", "message": "Session expired."}), 401

    wid = request.form.get("wid", "").strip()
    audit_type = request.form.get("audit_type", "").strip()

    if not wid: return jsonify({"status": "error", "message": "WID is required."}), 400

    inventory_df = context.get("inventory_df", pd.DataFrame())
    if inventory_df.empty: return jsonify({"status": "error", "message": "Inventory data not loaded on server."}), 500
    if 'wid' not in inventory_df.columns: return jsonify({"status": "error", "message": "WID column missing in Inventory.csv."}), 500

    match = inventory_df[inventory_df['wid'].astype(str).str.upper() == wid.upper()]
    if match.empty: return jsonify({"status": "error", "message": f"WID '{wid}' not found in Inventory."}), 404

    row = match.iloc[0]
    fsn = str(row.get('fsn', 'N/A')).strip()
    title = str(row.get('product_detail_product_title', 'N/A')).strip()

    vertical = "UNKNOWN"
    for col in inventory_df.columns:
        if 'vertical' in col.lower() or 'category' in col.lower():
            vertical = str(row[col]).strip()
            break

    is_applicable = False
    if vertical.lower() in AUDIT_RULES.get(audit_type, set()): is_applicable = True

    return jsonify({
        "status": "success", "fsn": fsn, "title": title, "vertical": vertical,
        "is_applicable": is_applicable,
        "message": "WID verified." if is_applicable else f"Vertical '{vertical}' is NOT applicable for this audit."
    })

@app.route("/api/submit_quality_audit", methods=["POST"])
def submit_quality_audit():
    context = get_user_context()
    if not context: return jsonify({"status": "error", "message": "Session expired."}), 401

    wid = request.form.get("wid", "").strip()
    qty = request.form.get("qty", "0").strip()
    pass_fail = request.form.get("pass_fail", "").strip()
    audit_type = request.form.get("audit_type", "").strip()
    fsn = request.form.get("fsn", "N/A")
    title = request.form.get("title", "N/A")
    vertical = request.form.get("vertical", "N/A")

    if not wid or not pass_fail or not qty: return jsonify({"status": "error", "message": "WID, Qty, and Pass/Fail are required."}), 400

    audit_no = generate_audit_no(audit_type, wid)
    evidence_file = request.files.get('evidence_image')
    image_name = save_evidence_image(evidence_file, audit_type, audit_no)

    timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    ldap_id = session.get('ldap_id', 'UNKNOWN')
    warehouse = session.get('warehouse_id', 'UNKNOWN')
    audit_category = AUDIT_CAT_MAP.get(audit_type, audit_type.replace('_', ' ').upper())

    with db_lock:
        conn = get_db_connection()
        try:
            conn.execute('''
                INSERT INTO master_audit_log ("Timestamp", "LDAP ID", "Warehouse", "Audit Category", "WID", "FSN", "Product", "Vertical", "Scanned Qty", "Expected Qty", "Status", "Audit No", "Image File")
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ''', (timestamp, ldap_id, warehouse, audit_category, wid, fsn, title, vertical, qty, qty, pass_fail, audit_no, image_name))
            conn.commit()
        finally:
            conn.close()

    data = {
        "Timestamp": timestamp, "LDAP ID": ldap_id, "Warehouse": warehouse,
        "Audit Category": audit_category, "WID": wid, "FSN": fsn,
        "Product": title, "Vertical": vertical, "Qty": qty, "Pass/Fail": pass_fail, 
        "Order ID": "N/A", "Linked Tracking": "N/A",
        "Audit No": audit_no, "Image File": image_name
    }
    safe_csv_export([data], f"{audit_type}_audit_NL.csv")

    return jsonify({"status": "success", "message": f"{audit_category} logged successfully!"})

@app.route("/api/submit_misship_audit", methods=["POST"])
def submit_misship_audit():
    context = get_user_context()
    if not context: return jsonify({"status": "error", "message": "Session expired."}), 401

    wsn = request.form.get("wsn", "").strip()
    rev_id = request.form.get("rev_id", "").strip()
    fsn = request.form.get("fsn", "").strip()
    title = request.form.get("title", "").strip()
    vertical = request.form.get("vertical", "").strip()
    pv_status = request.form.get("pv_status", "").strip()
    issue = request.form.get("issue", "").strip()
    sub_issue = request.form.get("sub_issue", "").strip()
    return_reason = request.form.get("return_reason", "").strip()

    audit_no = generate_audit_no("cx_misship", wsn)
    
    img_wsn = save_evidence_image(request.files.get('img_wsn'), "cx_misship", f"{audit_no}_wsn")
    img_mrp = save_evidence_image(request.files.get('img_mrp_label'), "cx_misship", f"{audit_no}_mrp")
    img_prod = save_evidence_image(request.files.get('img_product'), "cx_misship", f"{audit_no}_prod")

    img_combined = f"WSN:{os.path.basename(img_wsn)} | MRP:{os.path.basename(img_mrp)} | Prod:{os.path.basename(img_prod)}"

    timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    ldap_id = session.get('ldap_id', 'UNKNOWN')
    warehouse = session.get('warehouse_id', 'UNKNOWN')
    audit_category = "PV AUDIT"

    with db_lock:
        conn = get_db_connection()
        try:
            conn.execute('''
                INSERT INTO master_audit_log ("Timestamp", "LDAP ID", "Warehouse", "Audit Category", "Box/Tote ID", "FSN", "WID", "Product", "Vertical", "Expected Qty", "Scanned Qty", "Status", "WSN", "Rev ID", "Issue", "Sub Issue", "Return Reason", "PV Status", "Audit No", "Image File")
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ''', (timestamp, ldap_id, warehouse, audit_category, wsn, fsn, "N/A", title, vertical, 1, 1, pv_status, wsn, rev_id, issue, sub_issue, return_reason, pv_status, audit_no, img_combined))
            conn.commit()
        finally:
            conn.close()

    data = {
        "Timestamp": timestamp, "LDAP ID": ldap_id, "Warehouse": warehouse,
        "Audit Category": audit_category, "Box/Tote ID": wsn, "FSN": fsn,
        "Product": title, "Vertical": vertical, "Expected Qty": 1, "Scanned Qty": 1, 
        "Status": pv_status, "WSN": wsn, "Rev ID": rev_id, "Issue": issue, 
        "Sub Issue": sub_issue, "Return Reason": return_reason, "PV Status": pv_status,
        "WID": "N/A", "Order ID": "N/A", "Linked Tracking": "N/A",
        "Audit No": audit_no, "Image File": img_combined
    }
    safe_csv_export([data], "pv_audit_NL.csv")

    return jsonify({"status": "success", "message": "Misshipment Revalidation logged!"})

# =========================================================================
# --- CATALOGUE CORRECTION & MAPPING ---
# =========================================================================

@app.route("/api/get_shortages", methods=["GET"])
def get_shortages():
    context = get_user_context()
    if not context: return jsonify({"status": "error", "message": "Session expired."}), 401

    df = context.get("df", pd.DataFrame())
    scanned_items = context.get("scanned_items", {})
    
    expected_items = {str(row['Product']).strip(): row.to_dict() for _, row in df.iterrows()}

    multi_part_fsns = []
    if not df.empty and 'FSN' in df.columns and 'WID' in df.columns:
        fsn_groups = df.groupby('FSN')['WID'].nunique()
        multi_part_fsns = fsn_groups[fsn_groups > 1].index.tolist()

    short_items = []
    for name, details in expected_items.items():
        scan_qty = scanned_items.get(name, {"count": 0})["count"]
        exp_qty = int(details.get("Qty", 0))
        fsn = details.get("FSN", "")
        
        if scan_qty < exp_qty:
            if fsn in multi_part_fsns:
                continue 
            is_serialized = is_serialized_fsn(str(fsn).strip())
            verified_count = len(scanned_items.get(name, {}).get("serialized_records", [])) if is_serialized else None
            short_items.append({
                "name": name,
                "scanned": scan_qty,
                "expected": exp_qty,
                "fsn": str(fsn).strip(),
                "is_serialized": is_serialized,
                "verified_count": verified_count
            })

    return jsonify({"status": "success", "short_items": short_items})

@app.route("/api/map_catalogue", methods=["POST"])
def map_catalogue():
    context = get_user_context()
    if not context: return jsonify({"status": "error", "message": "Session expired."}), 401
    
    alien_ean = request.form.get("alien_ean")
    short_item_name = request.form.get("short_item_name")
    
    if alien_ean not in context["scanned_items"]:
        return jsonify({"status": "error", "message": "Alien EAN not found in session."}), 400

    if short_item_name not in context["scanned_items"]:
        expected_items = {str(row['Product']).strip(): row.to_dict() for _, row in context.get("df", pd.DataFrame()).iterrows()}
        if short_item_name in expected_items:
            context["scanned_items"][short_item_name] = {
                "count": 0,
                "expected_qty": int(expected_items[short_item_name].get("Qty", 0)),
                "fsn": expected_items[short_item_name].get("FSN", "N/A"),
                "wid": expected_items[short_item_name].get("WID", "N/A"),
                "type": "normal",
                "imei_mismatched": False
            }
        else:
            return jsonify({"status": "error", "message": "Short item not found in expected list."}), 400

    audit_no = generate_audit_no("cat_map", alien_ean)
    
    img_prod = save_evidence_image(request.files.get('img_product'), "catalogue", f"{audit_no}_prod")
    img_ean = save_evidence_image(request.files.get('img_ean'), "catalogue", f"{audit_no}_ean")
    img_mrp = save_evidence_image(request.files.get('img_mrp'), "catalogue", f"{audit_no}_mrp")

    alien_qty = context["scanned_items"][alien_ean]["count"]
    short_item = context["scanned_items"][short_item_name]
    
    short_item["count"] += alien_qty
    del context["scanned_items"][alien_ean]

    expected = short_item["expected_qty"]
    new_qty = short_item["count"]
    status = "OK"
    if new_qty > expected: status = "EXCESS"
    elif new_qty < expected: status = "SHORT"
    
    if short_item.get("imei_mismatched"):
        status += " (IMEI Mismatch)"

    timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    ldap_id = session.get('ldap_id', 'UNKNOWN')
    short_fsn = short_item.get('fsn', 'NA')
    short_wid = short_item.get('wid', 'N/A')

    pdf_path = ""
    pdf_filename = f"{audit_no}_{short_fsn}_{alien_ean}.pdf"
    
    if FPDF_AVAILABLE:
        try:
            def sanitize_pdf_text(text):
                if not text: return ""
                return str(text).replace('₹', 'Rs. ').replace('\u20b9', 'Rs. ').encode('latin-1', 'replace').decode('latin-1')

            class PDF(FPDF):
                def header(self):
                    self.set_font('Arial', 'B', 16)
                    self.set_text_color(40, 40, 40)
                    self.cell(0, 10, 'QPex Catalogue Correction Report', 0, 1, 'C')
                    self.line(10, 20, 287, 20)
                    self.ln(2)

            pdf = PDF(orientation='L', unit='mm', format='A4')
            pdf.add_page()
            
            pdf.set_font("Arial", 'B', 11)
            pdf.set_text_color(0, 0, 0)
            
            pdf.cell(30, 8, "Audit No:", 0, 0)
            pdf.set_font("Arial", '', 11)
            pdf.cell(65, 8, sanitize_pdf_text(audit_no), 0, 0)
            
            pdf.set_font("Arial", 'B', 11)
            pdf.cell(30, 8, "Date:", 0, 0)
            pdf.set_font("Arial", '', 11)
            pdf.cell(65, 8, sanitize_pdf_text(timestamp), 0, 0)
            
            pdf.set_font("Arial", 'B', 11)
            pdf.cell(30, 8, "Auditor ID:", 0, 0)
            pdf.set_font("Arial", '', 11)
            pdf.cell(0, 8, sanitize_pdf_text(ldap_id), 0, 1)
            
            pdf.set_font("Arial", 'B', 11)
            pdf.cell(30, 8, "Alien EAN:", 0, 0)
            pdf.set_font("Arial", '', 11)
            pdf.cell(65, 8, sanitize_pdf_text(alien_ean), 0, 0)

            pdf.set_font("Arial", 'B', 11)
            pdf.cell(30, 8, "Mapped FSN:", 0, 0)
            pdf.set_font("Arial", '', 11)
            pdf.cell(65, 8, sanitize_pdf_text(short_fsn), 0, 0)
            
            pdf.set_font("Arial", 'B', 11)
            pdf.cell(30, 8, "Transferred:", 0, 0)
            pdf.set_font("Arial", '', 11)
            pdf.cell(0, 8, sanitize_pdf_text(str(alien_qty)), 0, 1)

            pdf.set_font("Arial", 'B', 11)
            pdf.cell(35, 8, "Mapped Title:", 0, 0)
            pdf.set_font("Arial", '', 10)
            pdf.multi_cell(0, 8, sanitize_pdf_text(short_item_name[:120]))

            pdf.line(10, 48, 287, 48)
            
            y_img_title = 53
            y_img = 60
            img_width = 85
            x_pos = [15, 106, 197]
            
            labels = ["Product Image", "EAN Image", "MRP Label Image"]
            images = [img_prod, img_ean, img_mrp]
            
            for i in range(3):
                pdf.set_font("Arial", 'B', 12)
                pdf.text(x_pos[i] + 25, y_img_title, labels[i])
                if images[i] and os.path.exists(images[i]):
                    try:
                        pdf.image(images[i], x=x_pos[i], y=y_img, w=img_width)
                    except Exception as e:
                        pdf.set_font("Arial", '', 10)
                        pdf.text(x_pos[i] + 15, y_img + 20, f"Error Loading Image: {str(e)[:15]}")

            pdf_path = os.path.join(CATALOGUE_DIR, pdf_filename)
            pdf.output(pdf_path)
        except Exception as e:
            print(f"Failed to generate PDF: {e}")

    data = {
        "Timestamp": timestamp, "LDAP ID": ldap_id, 
        "Alien EAN": alien_ean, "Mapped FSN": short_fsn, "Mapped WID": short_wid,
        "Mapped Title": short_item_name, "Qty Transferred": alien_qty,
        "PDF Report": pdf_filename,
        "Img Product": os.path.basename(img_prod), "Img EAN": os.path.basename(img_ean), "Img MRP": os.path.basename(img_mrp)
    }
    safe_csv_export([data], "catalogue_corrections.csv")

    return jsonify({
        "status": "success", 
        "message": "Mapping successful and PDF generated.",
        "updated_item": {
            "name": short_item_name,
            "new_qty": f"{new_qty}/{expected}",
            "match": status,
            "removed_alien": alien_ean
        }
    })

# =========================================================================
# --- CORE SCRAPING AND AUDIT LOGIC ---
# =========================================================================

@app.route("/scan_box", methods=["POST"])
def scan_box():
    context = get_user_context()
    if not context: return jsonify({"status": "error", "message": "Session expired."}), 401

    box_id = request.form.get("box_id")
    if not box_id: return jsonify({"status": "error", "message": "No ID provided"}), 400

    audit_type = context.get("audit_type", "unit")
    
    if audit_type == 'hl_box_audit':
        # Redo is only honored if ALLOW_AUDIT_REDO is on. This check happens on the
        # backend, so even a request that sends force_redo=true is ignored when the
        # config is off — the frontend can't bypass it.
        force_redo = ALLOW_AUDIT_REDO and (request.form.get("force_redo", "false") == "true")
        if not force_redo:
            with db_lock:
                conn = get_db_connection()
                try:
                    existing = conn.execute('SELECT "Timestamp" FROM master_audit_log WHERE "Box/Tote ID" = ? AND "Audit Category" = ?', (box_id, 'NCOB BOX AUDIT')).fetchone()
                finally:
                    conn.close()
            if existing:
                if ALLOW_AUDIT_REDO:
                    message = f"Box {box_id} was already audited on {existing['Timestamp']}. Do you want to redo it?"
                else:
                    message = f"Box {box_id} was already audited on {existing['Timestamp']}. Redo is disabled."
                return jsonify({"status": "warning", "already_audited": True, "allow_redo": ALLOW_AUDIT_REDO, "message": message})

    pool_member = None
    if audit_type == 'hl_box_audit':
        pool_member = acquire_ncob_pool_driver()
        if not pool_member:
            return jsonify({"status": "error", "message": "All NCOB scraper sessions are busy. Please retry in a moment."}), 503
        driver = pool_member["driver"]
    else:
        driver = ensure_personal_driver(context)
        if not driver:
            return jsonify({"status": "error", "message": "Session driver unavailable. Please log in again."}), 401

    # Switch Window if needed
    try:
        if audit_type == 'hl_box_audit':
            try: driver.switch_to.window(driver.window_handles[1])
            except IndexError:
                driver.execute_script("window.open('http://10.24.1.71/flo-lite', '_blank');")
                driver.switch_to.window(driver.window_handles[1])
        else: 
            driver.switch_to.window(driver.window_handles[0])
    except Exception:
        if pool_member: release_ncob_pool_driver(pool_member)
        return jsonify({"status": "error", "message": "Could not prepare scraper session. Please retry."}), 500

    url_map = {
        'unit': "http://10.24.1.53/inventory/view_store_inventory",
        'bulk': "http://10.24.1.53/inventory/view_store_inventory",
        'picklist': "http://10.24.1.53/storage_locations/view_tote",
        'putlist': "http://10.24.1.53/inventory/find_putlists",
        'ob_audit': "http://10.24.1.53/shipments/find_shipments",
        'hl_box_audit': f"http://10.24.1.71/flo-lite/{session.get('warehouse_flolite')}/v2/ncob/packing/scan/view-box"
    }
    
    target_url = url_map.get(audit_type)
    if target_url:
        try:
            driver.get(target_url)
            time.sleep(1.5)
        except Exception:
            pass

    context.update({"scanned_items": {}, "df": pd.DataFrame(), "scan_history": [], "box_id": box_id})
    extracted_data = []

    try:
        wait = WebDriverWait(driver, 10)
        
        # ── 1. NCOB Box Audit ──
        if audit_type == 'hl_box_audit':
            api_details = api_get_container_details(driver, box_id, session.get('warehouse_flolite', ''))
            api_items = (api_details or {}).get("items") if isinstance(api_details, dict) else None

            if api_items:
                # Direct API path - no page load/DOM wait needed at all.
                seen = {}
                for item in api_items:
                    fsn = str(item.get("fsn") or "").strip()
                    product = str(item.get("product_title") or "").strip()
                    qty = int(item.get("quantity") or 0)
                    wid = str(item.get("wid") or "N/A").strip() or "N/A"
                    if not fsn:
                        continue
                    key = (fsn, product)
                    if key in seen:
                        seen[key]["Qty"] += qty
                    else:
                        seen[key] = {"FSN": fsn, "Product": product, "Qty": qty, "WID": wid}
                extracted_data.extend(seen.values())

            if not api_items:
                # Fallback: original Selenium DOM-scrape of the view-box page.
                input_elem = wait.until(EC.element_to_be_clickable((By.XPATH, "/html/body/div[1]/div/div/div/div[2]/div/div[2]/div[1]/div/div[1]/input")))
                input_elem.clear()
                input_elem.send_keys(box_id + Keys.RETURN)

                wait.until(EC.visibility_of_element_located((By.XPATH, "/html/body/div[1]/div/div/div/div[2]/div/div[2]/div[2]/div[4]/span[2]")))
                item_blocks = driver.find_elements(By.CSS_SELECTOR, "div[data-testid]")
                raw_data = []
                for block in item_blocks:
                    lines = [line.strip() for line in block.text.split('\n') if line.strip()]
                    if len(lines) < 3: continue
                    if lines[0].upper() == "FSN" and len(lines) > 1:
                        fsn = lines[1].strip()
                        product = " ".join(lines[2:-1]).strip()
                    else:
                        fsn = lines[0].split(':')[-1].strip()
                        product = " ".join(lines[1:-1]).strip()
                    qty = lines[-1].split(':')[-1].strip()
                    raw_data.append([fsn, product, qty])

                seen = {}
                for row in raw_data:
                    key = (row[0], row[1])
                    if key in seen:
                        try: seen[key][2] = str(int(seen[key][2]) + int(row[2]))
                        except Exception: pass
                    else: seen[key] = list(row)
                for fsn, product, qty in seen.values():
                    extracted_data.append({"FSN": fsn, "Product": product, "Qty": qty, "WID": "N/A"})

        # ── 2. Bin / Bulk Audit ──
        elif audit_type in ['unit', 'bulk']:
            input_elem = wait.until(EC.element_to_be_clickable((By.ID, "filters_location")))
            input_elem.clear()
            input_elem.send_keys(box_id + Keys.RETURN)
            
            # Using robust relative XPaths instead of fragile absolute paths
            table_xpath = "//div[@id='inventory_table']//table"
            headers_xpath = f"{table_xpath}/thead[contains(@class, 'tableFloatingHeaderOriginal')]/tr[2]/th"
            
            header_elements = wait.until(EC.presence_of_all_elements_located((By.XPATH, headers_xpath)))
            headers = [h.text.strip() for h in header_elements]
            
            data_rows = driver.find_elements(By.XPATH, f"{table_xpath}/tbody/tr")
            for row in data_rows:
                cols = row.find_elements(By.TAG_NAME, "td")
                if len(cols) > 0:
                    # Zip headers and cols up to the minimum length to avoid out-of-bounds mismatches
                    limit = min(len(headers), len(cols))
                    extracted_data.append(dict(zip(headers[:limit], [c.text.strip() for c in cols[:limit]])))

        # ── 3. Picklist Audit ──
        elif audit_type == 'picklist':
            input_elem = wait.until(EC.presence_of_element_located((By.XPATH, "/html/body/div[3]/div[1]/form/div/div/div/div[1]/input[2]")))
            input_elem.clear()
            input_elem.send_keys(box_id + Keys.RETURN)
            
            data_rows_xpath = "/html/body/div[3]/div[1]/div[4]/div[3]/div/div[5]/table/tbody/tr"
            data_rows = wait.until(EC.presence_of_all_elements_located((By.XPATH, data_rows_xpath)))
            for row in data_rows:
                fsn_text = row.find_element(By.XPATH, "./td[1]/div[1]").text.strip()
                fsn = fsn_text.split('\n')[0].split(':')[1].strip() if ':' in fsn_text else fsn_text
                product = row.find_element(By.XPATH, "./td[2]/div[1]").text.strip()
                qty = row.find_element(By.XPATH, "./td[3]").text.strip()
                extracted_data.append({"FSN": fsn, "Product": product, "Qty": qty, "WID": "N/A"})

        # ── 4. Putlist Audit ──
        elif audit_type == 'putlist':
            possible_input_xpaths = ["/html/body/div[3]/div[1]/div[2]/form/div[2]/input", "/html/body/div[3]/div[1]/div[2]/form/div[8]/div[2]/input"]
            submit_button_xpath = "/html/body/div[3]/div[1]/div[2]/form/div[8]/div[6]/input[1]"
            details_link_xpath = "/html/body/div[3]/div[1]/div[4]/form/div/div[1]/table/tbody/tr/td[1]/a"
            
            link_found_and_clicked = False
            short_wait = WebDriverWait(driver, 5)

            for input_xpath in possible_input_xpaths:
                if link_found_and_clicked: break
                for method in ["RETURN_KEY", "BUTTON_CLICK"]:
                    try:
                        driver.get(target_url) 
                        time.sleep(1)
                        input_elem = driver.find_element(By.XPATH, input_xpath)
                        input_elem.clear()
                        input_elem.send_keys(box_id)

                        if method == "RETURN_KEY":
                            input_elem.send_keys(Keys.RETURN)
                            driver.find_element(By.XPATH, submit_button_xpath).click()
                        elif method == "BUTTON_CLICK":
                            driver.find_element(By.XPATH, submit_button_xpath).click()

                        details_link = short_wait.until(EC.element_to_be_clickable((By.XPATH, details_link_xpath)))
                        details_link.click()
                        link_found_and_clicked = True
                        break 
                    except (NoSuchElementException, TimeoutException):
                        try: driver.find_element(By.XPATH, input_xpath).clear()
                        except NoSuchElementException: pass
                        continue 

            if not link_found_and_clicked:
                return jsonify({"status": "error", "message": f"Error: Could not find details for Tote ID '{box_id}'."}), 404

            try:
                long_wait = WebDriverWait(driver, 12)
                try: putlist_id_val = driver.find_element(By.XPATH, "/html/body/div[3]/div[1]/div[2]/div[1]/table/tbody/tr/td[1]").text.strip()
                except NoSuchElementException: putlist_id_val = "N/A"

                headers_xpath = "/html/body/div[3]/div[1]/div[2]/div[2]/table/tbody[1]/tr/th"
                long_wait.until(EC.visibility_of_element_located((By.XPATH, headers_xpath)))
                header_elements = driver.find_elements(By.XPATH, headers_xpath)
                headers = [h.text.strip() for h in header_elements]

                data_rows_xpath = "/html/body/div[3]/div[1]/div[2]/div[2]/table/tbody[2]/tr"
                data_rows = driver.find_elements(By.XPATH, data_rows_xpath)
                for row in data_rows:
                    cols = row.find_elements(By.TAG_NAME, "td")
                    if len(cols) >= len(headers):
                        row_values = [c.text.strip() for c in cols[:len(headers)]]
                        row_dict = dict(zip(headers, row_values))
                        row_dict["Putlist ID"] = putlist_id_val
                        extracted_data.append(row_dict)
            except (NoSuchElementException, TimeoutException):
                return jsonify({"status": "error", "message": "Error: Could not find the data table on details page."}), 500

        # ── 5. Customer Outbound Audit ──
        elif audit_type == 'ob_audit':
            input_elem = wait.until(EC.presence_of_element_located((By.ID, "tracking_id")))
            input_elem.clear()
            input_elem.send_keys(box_id)

            for cb_id in ["filters_include_status_date", "filters_include_dispatch_date"]:
                try:
                    cb = driver.find_element(By.ID, cb_id)
                    if cb.is_selected(): cb.click()
                except Exception: pass

            submit_btn = driver.find_element(By.XPATH, "//input[@value=' Find Shipments ']")
            submit_btn.click()

            try:
                table_xpath = "/html/body/div[3]/div[1]/div[5]/div[4]/table/tbody/tr"
                wait.until(EC.visibility_of_element_located((By.XPATH, table_xpath)))
                data_rows = driver.find_elements(By.XPATH, table_xpath)
                
                linked_tracking = "N/A"
                try:
                    linked_elem = driver.find_element(By.XPATH, "/html/body/div[3]/div[1]/div[4]/form/div/div[1]/table/tbody/tr/td[4]")
                    linked_tracking = linked_elem.text.strip()
                except Exception: pass
                
                for row in data_rows:
                    cols = row.find_elements(By.TAG_NAME, "td")
                    if len(cols) >= 6:
                        fsn_text = cols[0].text.strip()
                        fsn_match = re.search(r'FSN:\s*([A-Z0-9]+)', fsn_text)
                        fsn = fsn_match.group(1) if fsn_match else fsn_text.split('\n')[0].strip()
                        
                        wid_match = re.search(r'WID:\s*([A-Z0-9]+)', fsn_text)
                        wid = wid_match.group(1) if wid_match else "N/A"
                        
                        product = cols[1].text.strip()
                        qty = cols[5].text.strip()
                        
                        order_id = cols[4].text.strip() if len(cols) > 4 else "N/A"

                        imei_match = re.search(r'IMEI Number:\s*\[\s*([A-Za-z0-9\-\_]+)\s*\]', product)
                        expected_imei = imei_match.group(1) if imei_match else ""
                        
                        extracted_data.append({
                            "FSN": fsn, "Product": product, "Qty": qty, "WID": wid, 
                            "Expected_IMEI": expected_imei, "Order_ID": order_id, 
                            "Linked_Tracking": linked_tracking
                        })
            except TimeoutException:
                pass 

        # ── 6. PV Audit ──
        elif audit_type == 'cx_misship':
            try:
                # Primary Attempt: get_wsn_location
                driver.get("http://10.24.1.53/returns/get_wsn_location")
                input_elem = wait.until(EC.element_to_be_clickable((By.XPATH, "/html/body/div[3]/div[1]/div[3]/form/div[1]/input")))
                input_elem.clear()
                input_elem.send_keys(box_id)
                driver.find_element(By.XPATH, "/html/body/div[3]/div[1]/div[3]/form/div[2]/input").click()
                
                # Wait for the results div to load
                wait.until(EC.presence_of_element_located((By.XPATH, "/html/body/div[3]/div[1]/div[7]")))
                
                # Scrape Table 1 for Rev ID (Return Shipment Id)
                t1_rows = driver.find_elements(By.XPATH, "/html/body/div[3]/div[1]/div[7]/div[1]//tr")
                rev_id = ""
                for row in t1_rows:
                    cols = row.find_elements(By.TAG_NAME, "td")
                    if len(cols) >= 2 and "Return Shipment Id" in cols[0].text:
                        try:
                            rev_id = cols[1].find_element(By.TAG_NAME, "a").text.strip()
                        except:
                            rev_id = cols[1].text.strip()
                        break
                        
                # Scrape Table 2 for Product Details
                t2_rows = driver.find_elements(By.XPATH, "/html/body/div[3]/div[1]/div[7]/div[2]//tr")
                fsn, title, vertical = "", "", ""
                for row in t2_rows:
                    cols = row.find_elements(By.TAG_NAME, "td")
                    if len(cols) >= 2:
                        label = cols[0].text.strip().lower()
                        if label == "fsn": fsn = cols[1].text.strip()
                        elif label == "title": title = cols[1].text.strip()
                        elif label == "vertical": vertical = cols[1].text.strip()

                if not rev_id or not fsn:
                    raise Exception("Missing vital details in get_wsn_location.")

                extracted_data.append({
                    "FSN": fsn, "Product": title, "Qty": 1, "WID": "N/A", 
                    "Rev_ID": rev_id, "Vertical": vertical, "Return_Reason": "Data Extracted via WSN Location"
                })

            except Exception as e1:
                print(f"get_wsn_location failed: {e1}, attempting fallback to trace_wsn...")
                try:
                    # Fallback Attempt: trace_wsn
                    driver.get("http://10.24.1.53/returns/trace_wsn")
                    input_elem = wait.until(EC.element_to_be_clickable((By.XPATH, "/html/body/div[3]/div[1]/div[3]/form/div[1]/input")))
                    input_elem.clear()
                    input_elem.send_keys(box_id)
                    
                    trace_search_btn_xpath = "/html/body/div[3]/div[1]/div[3]/form/div[2]/input"
                    driver.find_element(By.XPATH, trace_search_btn_xpath).click()
                    
                    # Robust extraction of Rev ID (Return Shipment Id) inside the table
                    table_xpath = "/html/body/div[3]/div/div[7]/div[1]/div/table"
                    try:
                        wait.until(EC.visibility_of_element_located((By.XPATH, table_xpath)))
                    except TimeoutException:
                        driver.find_element(By.XPATH, trace_search_btn_xpath).click()
                        wait.until(EC.visibility_of_element_located((By.XPATH, table_xpath)))
                    
                    rows = driver.find_elements(By.XPATH, f"{table_xpath}/tbody/tr")
                    rev_id = ""
                    for row in rows:
                        cols = row.find_elements(By.TAG_NAME, "td")
                        if len(cols) >= 2 and "Return Shipment Id" in cols[0].text:
                            try:
                                rev_id = cols[1].find_element(By.TAG_NAME, "a").text.strip()
                            except:
                                rev_id = cols[1].text.strip()
                            break
                    
                    if not rev_id:
                        rev_id = "Scraping Error"
                    
                    driver.get("http://10.24.1.53/returns/pv_for_received_shipment")
                    pv_input = wait.until(EC.element_to_be_clickable((By.XPATH, "/html/body/div[3]/div[1]/div[3]/form/div[2]/input")))
                    pv_input.clear()
                    pv_input.send_keys(rev_id)
                    driver.find_element(By.XPATH, "/html/body/div[3]/div[1]/div[3]/form/div[6]/input").click()
                    
                    # Robust XPath Fallbacks
                    try:
                        wait.until(EC.presence_of_element_located((By.XPATH, "/html/body/div[3]/div[1]/div[5]/div[4]/table/tbody[2]/tr[2]")))
                    except TimeoutException:
                        try:
                            wait.until(EC.presence_of_element_located((By.XPATH, "/html/body/div[3]/div[1]/div[5]/div[1]/div[2]/table/tbody[2]/tr[2]")))
                        except TimeoutException:
                            pass
                    
                    try:
                        fsn = driver.find_element(By.XPATH, "/html/body/div[3]/div[1]/div[5]/div[4]/table/tbody[2]/tr[2]/td[1]/a").text.strip()
                    except NoSuchElementException:
                        try:
                            fsn = driver.find_element(By.XPATH, "/html/body/div[3]/div[1]/div[5]/div[1]/div[2]/table/tbody[2]/tr[2]/td[1]/a").text.strip()
                        except:
                            fsn = "Scraping Error"
                        
                    try:
                        vertical = driver.find_element(By.XPATH, "/html/body/div[3]/div[1]/div[5]/div[4]/table/tbody[2]/tr[2]/td[3]").text.strip()
                    except NoSuchElementException:
                        try:
                            vertical = driver.find_element(By.XPATH, "/html/body/div[3]/div[1]/div[5]/div[1]/div[2]/table/tbody[2]/tr[2]/td[2]").text.strip()
                        except:
                            vertical = "Scraping Error"
                        
                    try:
                        title = driver.find_element(By.XPATH, "/html/body/div[3]/div[1]/div[5]/div[4]/table/tbody[2]/tr[2]/td[5]").text.strip()
                    except NoSuchElementException:
                        try:
                            title = driver.find_element(By.XPATH, "/html/body/div[3]/div[1]/div[5]/div[1]/div[2]/table/tbody[2]/tr[2]/td[4]").text.strip()
                        except:
                            title = "Scraping Error - Please Verify Manually"
                    
                    try:
                        r_text = driver.find_element(By.XPATH, "/html/body/div[3]/div[1]/div[5]/table/tbody/tr/td").text.strip()
                    except NoSuchElementException:
                        try:
                            r_text = driver.find_element(By.XPATH, "/html/body/div[3]/div[1]/div[5]/div[1]/div[2]/table/tbody[2]/tr[2]").text.strip()
                        except:
                            r_text = "Scraping Error - Could not retrieve return reason."

                    extracted_data.append({
                        "FSN": fsn, "Product": title, "Qty": 1, "WID": "N/A", 
                        "Rev_ID": rev_id, "Vertical": vertical, "Return_Reason": r_text
                    })

                except Exception as outer_e:
                    print(f"Total scraping failure for PV Audit: {outer_e}")
                    # Ultimate fallback to allow manual audit
                    extracted_data.append({
                        "FSN": "Scraping Error", 
                        "Product": "Scraping Error - Please Proceed with Manual Audit", 
                        "Qty": 1, 
                        "WID": "N/A", 
                        "Rev_ID": "Scraping Error", 
                        "Vertical": "N/A", 
                        "Return_Reason": "Scraping Error - Could not extract details."
                    })

        if not extracted_data:
            return jsonify({"status": "error", "message": "Bin/Tote/Tracking ID/WSN is empty or not found."}), 404

        if audit_type == 'cx_misship':
            return jsonify({"status": "success", "message": "WSN Processed successfully", "extracted_data": extracted_data})

        context["df"] = pd.DataFrame(extracted_data)

        if audit_type == 'hl_box_audit' and pool_member:
            log_ncob_snapshot(box_id, extracted_data, pool_member["ldap_id"], session.get('ldap_id', 'UNKNOWN'))
        
        # Cast to str globally to avoid JSON parsing crashes
        if 'Product' in context["df"].columns:
            context["df"]['Product'] = context["df"]['Product'].astype(str)
            
        if audit_type == 'putlist':
            if 'FSN/SKU/WID' in context["df"].columns:
                context["df"]['FSN'] = context["df"]['FSN/SKU/WID'].apply(lambda x: x.split('FSN:')[1].split('\n')[0].strip() if isinstance(x, str) and 'FSN:' in x else None)
            if 'Item Description' in context["df"].columns:
                context["df"].rename(columns={'Item Description': 'Product'}, inplace=True)

        if 'Qty' in context["df"].columns: context["df"]['Qty'] = pd.to_numeric(context["df"]['Qty'], errors='coerce').fillna(0)
        if 'FSN' not in context["df"].columns and 'fsn' in context["df"].columns: context["df"].rename(columns={'fsn': 'FSN'}, inplace=True)
        if 'WID' not in context["df"].columns and 'wid' in context["df"].columns: context["df"].rename(columns={'wid': 'WID'}, inplace=True)

        if 'WID' not in context["df"].columns:
            context["df"]['WID'] = "N/A"

        def make_unique_product(row):
            p = str(row.get('Product', '')).strip()
            w = str(row.get('WID', 'N/A')).strip()
            if w and w != "N/A" and f"[WID:{w}]" not in p:
                return f"{p} [WID:{w}]"
            return p
        
        if not context["df"].empty:
            context["df"]['Product'] = context["df"].apply(make_unique_product, axis=1)

        # --- Expiry Checking ---
        expired_alerts = []
        if audit_type in ['unit', 'bulk'] and ENABLE_WID_SCAN:
            inventory_df = context.get("inventory_df", pd.DataFrame())
            if not inventory_df.empty:
                exp_col = next((c for c in inventory_df.columns if 'expir' in c.lower() or 'shelf' in c.lower()), None)
                today_date = pd.Timestamp(datetime.now().date())

                for idx in context["df"].index:
                    row = context["df"].loc[idx]
                    wid = str(row.get("WID", "")).strip()
                    fsn = str(row.get("FSN", "")).strip()
                    if wid == "nan": wid = ""
                    if fsn == "nan": fsn = ""
                    
                    match = pd.DataFrame()
                    if wid and wid != "N/A":
                        if 'wid' in inventory_df.columns:
                            match = inventory_df[inventory_df['wid'].astype(str).str.upper() == wid.upper()]
                    
                    if match.empty and fsn and fsn != "N/A":
                        if 'fsn' in inventory_df.columns:
                            match = inventory_df[inventory_df['fsn'].astype(str).str.upper() == fsn.upper()]

                    if not match.empty:
                        m_row = match.iloc[0]
                        
                        if not wid or wid == "N/A":
                            new_wid = str(m_row.get('wid', 'N/A'))
                            context["df"].loc[idx, 'WID'] = new_wid
                            wid = new_wid
                            if wid != "N/A":
                                current_p = context["df"].loc[idx, 'Product']
                                if f"[WID:{wid}]" not in current_p:
                                    context["df"].loc[idx, 'Product'] = f"{current_p} [WID:{wid}]"
                        
                        if exp_col:
                            exp_val = m_row.get(exp_col)
                            if pd.notna(exp_val) and str(exp_val).strip():
                                try:
                                    exp_date = pd.to_datetime(str(exp_val).strip(), dayfirst=True)
                                    if pd.notna(exp_date) and exp_date < today_date + pd.Timedelta(days=1):
                                        title = str(row.get("Product", m_row.get('product_detail_product_title', ''))).strip()
                                        qty = int(row.get("Qty", 0))
                                        exp_str = exp_date.strftime('%d-%m-%Y')
                                        expired_alerts.append({
                                            "wid": wid,
                                            "fsn": str(m_row.get('fsn', fsn)),
                                            "title": title,
                                            "qty": qty,
                                            "expiry_date": exp_str
                                        })
                                except Exception:
                                    pass

        return jsonify({"status": "success", "message": f"{audit_type.replace('_', ' ').title()} scanned! Ready for items.", "expired_alerts": expired_alerts})
    except Exception as e:
        return jsonify({"status": "error", "message": f"An error occurred: {str(e)}"}), 500
    finally:
        if pool_member:
            release_ncob_pool_driver(pool_member)

@app.route("/scan_product", methods=["POST"])
def scan_product():
    context = get_user_context()
    if not context or context.get("df") is None or context["df"].empty:
        return jsonify({"status": "error", "message": "Please scan a box or tote first."}), 400

    scanned_value = request.form.get("scanned_ean", "").strip()
    quantity = int(request.form.get("quantity", 1))
    scanned_imei = request.form.get("scanned_imei", "").strip()
    scanned_wid = request.form.get("scanned_wid", "").strip()
    serialized_wsn = request.form.get("serialized_wsn", "").strip()
    serialized_imei1 = request.form.get("serialized_imei1", "").strip()
    serialized_imei2 = request.form.get("serialized_imei2", "").strip()
    
    if not scanned_value: return jsonify({"status": "error", "message": "Input cannot be empty."}), 400

    df = context["df"]
    scanned_items = context["scanned_items"]
    audit_type = context["audit_type"]
    inventory_df = context.get("inventory_df", pd.DataFrame())
    
    matched_row = None
    item_type = 'normal'

    def get_best_match(match_df):
        if match_df.empty: return None
        if scanned_imei and 'Expected_IMEI' in match_df.columns:
            imei_match_df = match_df[match_df['Expected_IMEI'].astype(str).str.upper() == scanned_imei.upper()]
            if not imei_match_df.empty:
                return imei_match_df.iloc[0]
                
        for _, r in match_df.iterrows():
            prod_name = str(r.get("Product", "")).strip()
            current_count = scanned_items.get(prod_name, {}).get("count", 0)
            exp_qty = int(r.get("Qty", 0))
            if current_count < exp_qty:
                return r
        return match_df.iloc[0]

    # Check directly inside the scraped box (df)
    if ENABLE_WID_SCAN and 'WID' in df.columns:
        match = df[df['WID'].astype(str).str.upper() == scanned_value.upper()]
        if not match.empty:
            matched_row = get_best_match(match)

    if matched_row is None:
        fsn_to_match = scanned_value[3:19] if scanned_value.upper().startswith("LST") else scanned_value
        if 'FSN' in df.columns:
            match_df = df[df['FSN'].astype(str).str.upper() == fsn_to_match.upper()]
            if not match_df.empty:
                if len(match_df) > 1:
                    unique_wids = [w for w in match_df['WID'].astype(str).unique() if w != 'N/A' and str(w).lower() != 'nan']
                    if len(unique_wids) > 1:
                        # Bypass WID Verification if IMEI is present
                        has_imei = False
                        if 'Expected_IMEI' in match_df.columns:
                            has_imei = any(pd.notna(r.get('Expected_IMEI')) and str(r.get('Expected_IMEI')).strip() for _, r in match_df.iterrows())
                        
                        if not has_imei:
                            if not scanned_wid:
                                return jsonify({"status": "require_wid", "message": "Multi-part product detected. Please scan WID to verify the exact part."})
                            else:
                                match_df = match_df[match_df['WID'].astype(str).str.upper() == scanned_wid.upper()]
                                if match_df.empty:
                                    return jsonify({"status": "error", "message": f"WID {scanned_wid} does not belong to this product FSN."})
                matched_row = get_best_match(match_df)
    
    if matched_row is None and scanned_value.isnumeric():
        match_rows = []
        for _, row in df.iterrows():
            if scanned_value in str(row.get("Product", "")):
                match_rows.append(row)
        if match_rows:
            match_df = pd.DataFrame(match_rows)
            if len(match_df) > 1:
                unique_wids = [w for w in match_df['WID'].astype(str).unique() if w != 'N/A' and str(w).lower() != 'nan']
                if len(unique_wids) > 1:
                    # Bypass WID Verification if IMEI is present
                    has_imei = False
                    if 'Expected_IMEI' in match_df.columns:
                        has_imei = any(pd.notna(r.get('Expected_IMEI')) and str(r.get('Expected_IMEI')).strip() for _, r in match_df.iterrows())
                    
                    if not has_imei:
                        if not scanned_wid:
                            return jsonify({"status": "require_wid", "message": "Multi-part product detected. Please scan WID to verify the exact part."})
                        else:
                            match_df = match_df[match_df['WID'].astype(str).str.upper() == scanned_wid.upper()]
                            if match_df.empty:
                                return jsonify({"status": "error", "message": f"WID {scanned_wid} does not belong to this product."})
            matched_row = get_best_match(match_df)

    # --- UNIVERSAL GLOBAL INVENTORY LOOKUP FOR ALL AUDITS ---
    if matched_row is None and not inventory_df.empty:
        matches = pd.DataFrame()
        scan_upper = scanned_value.upper()
        
        # 1. Search WID Columns
        wid_cols = [c for c in inventory_df.columns if 'wid' in c.lower()]
        for c in wid_cols:
            matches = inventory_df[inventory_df[c].astype(str).str.upper() == scan_upper]
            if not matches.empty: break
            
        # 2. Search FSN Columns
        if matches.empty:
            fsn_to_match = scanned_value[3:19] if scan_upper.startswith("LST") else scanned_value
            fsn_cols = [c for c in inventory_df.columns if 'fsn' in c.lower()]
            for c in fsn_cols:
                matches = inventory_df[inventory_df[c].astype(str).str.upper() == fsn_to_match.upper()]
                if not matches.empty: break
                
        # 3. Search EAN Columns explicitly
        if matches.empty and scanned_value.isnumeric():
            ean_cols = [c for c in inventory_df.columns if 'ean' in c.lower()]
            for c in ean_cols:
                matches = inventory_df[inventory_df[c].astype(str).str.contains(scanned_value, case=False, na=False)]
                if not matches.empty: break
                
        # 4. Search Product Title / Description fallback
        if matches.empty and scanned_value.isnumeric():
            title_cols = []
            if 'product_detail_product_title' in inventory_df.columns:
                title_cols.append('product_detail_product_title')
            else:
                title_cols = [c for c in inventory_df.columns if 'title' in c.lower() or 'desc' in c.lower()]
            for c in title_cols:
                matches = inventory_df[inventory_df[c].astype(str).str.contains(scanned_value, case=False, na=False)]
                if not matches.empty: break

        if not matches.empty:
            match_data = matches.iloc[0]
            item_type = 'misship'
            
            if 'product_detail_product_title' in inventory_df.columns:
                title_col = 'product_detail_product_title'
            else:
                title_col = next((c for c in inventory_df.columns if 'title' in c.lower() or 'desc' in c.lower()), None)
            
            title_val = str(match_data[title_col]).strip() if title_col else scanned_value
            
            fsn_col = next((c for c in inventory_df.columns if 'fsn' in c.lower()), None)
            fsn_val = str(match_data[fsn_col]).strip() if fsn_col else 'N/A'
            
            wid_col = next((c for c in inventory_df.columns if 'wid' in c.lower()), None)
            wid_val = str(match_data[wid_col]).strip() if wid_col else 'N/A'

            matched_row = pd.Series({
                "Product": title_val,
                "Qty": 0, "FSN": fsn_val, "WID": wid_val
            })
        else:
            item_type = 'alien'

    item_name = str(matched_row["Product"]).strip() if matched_row is not None else scanned_value
    expected_qty = int(matched_row.get("Qty", 0)) if matched_row is not None else 0

    expected_imei = ""
    if matched_row is not None and "Expected_IMEI" in matched_row:
        val = matched_row["Expected_IMEI"]
        if pd.notna(val) and val:
            expected_imei = str(val).strip()

    imei_mismatched = False
    if expected_imei:
        if not scanned_imei:
            return jsonify({"status": "require_imei", "message": "IMEI required for this product."})
        if scanned_imei.upper() != expected_imei.upper():
            imei_mismatched = True

    # --- SERIALIZED FSN CAPTURE (NCOB Box Audit only) ---
    # WSN + IMEI1/Serialized Number are mandatory, IMEI2 optional. Also verified against
    # the backend (get_wsn_location, see wsn_mismatched below) once both are present.
    # Blocks the scan (same pattern as require_wid/require_imei) until the popup's
    # fields come back.
    matched_fsn_for_serial = str(matched_row.get("FSN", "N/A")).strip() if matched_row is not None else "N/A"
    needs_serial_capture = (audit_type == 'hl_box_audit') and is_serialized_fsn(matched_fsn_for_serial)
    requested_quantity = quantity  # snapshot before it gets forced to 1 below

    # Serialized items are captured one unit at a time, enforced here (not just in the UI):
    # no matter what quantity the client sends, at most 1 unit is ever added per call when
    # the FSN is serialized. This is what actually prevents someone from scanning WSN/IMEI
    # once and claiming a Qty of 3 - the popup (and this cap) forces 3 separate calls.
    if needs_serial_capture:
        quantity = 1

    if needs_serial_capture and not (serialized_wsn and serialized_imei1):
        return jsonify({
            "status": "require_serialized_scan",
            "message": "Serialized product detected. Please scan WSN and IMEI1/Serialized Number.",
            "fsn": matched_fsn_for_serial,
            "item_name": item_name,
            "is_mobile": is_mobile_fsn(matched_fsn_for_serial),
            "requested_qty": requested_quantity
        })

    if needs_serial_capture:
        is_mobile_item = is_mobile_fsn(matched_fsn_for_serial)
        if is_mobile_item:
            # Mobiles: IMEI1 must be a real IMEI (15 digits, Luhn checksum). IMEI2 is
            # optional but if something was entered, it must be valid too.
            if not is_valid_imei(serialized_imei1):
                return jsonify({"status": "error", "message": "Invalid IMEI 1. It must be a real 15-digit IMEI - please rescan.", "fsn": matched_fsn_for_serial, "is_mobile": True})
            if serialized_imei2 and not is_valid_imei(serialized_imei2):
                return jsonify({"status": "error", "message": "Invalid IMEI 2. It must be a real 15-digit IMEI - please rescan.", "fsn": matched_fsn_for_serial, "is_mobile": True})
        else:
            # Non-mobiles have no checksum to verify, so instead this blocks the lazy
            # bypass of re-scanning an already-known identifier (the box's own FSN/EAN/
            # WID, or the WSN just entered in this same popup) as a stand-in "serial
            # number" instead of the actual serial printed on the unit.
            box_wid = str(matched_row.get("WID", "")).strip().upper() if matched_row is not None else ""
            forbidden_values = {matched_fsn_for_serial.strip().upper(), scanned_value.strip().upper(), box_wid, serialized_wsn.strip().upper()} - {""}
            if serialized_imei1.strip().upper() in forbidden_values:
                return jsonify({"status": "error", "message": "Serial Number can't be the same as this product's FSN/EAN/WID/WSN - please scan the serial number printed on the unit.", "fsn": matched_fsn_for_serial, "is_mobile": False})
            if serialized_imei2 and serialized_imei2.strip().upper() in forbidden_values:
                return jsonify({"status": "error", "message": "Serial Number 2 can't be the same as this product's FSN/EAN/WID/WSN.", "fsn": matched_fsn_for_serial, "is_mobile": False})

    # Backend verification: confirm the scanned WSN is real and belongs to this unit,
    # by cross-checking get_wsn_location's "Title" against the matched product and its
    # "Return Serial Numbers" against the IMEI1/serial the auditor scanned. A lookup
    # failure/timeout blocks the scan (retried internally) rather than letting it
    # through unverified. A completed lookup that doesn't match also blocks - the
    # rejected attempt is logged to the audit-trail CSV first (Result=REJECTED) so the
    # trail shows what was scanned before the eventually-accepted (Result=ACCEPTED) scan.
    # The frontend already calls /api/verify_wsn the moment the WSN is scanned, well
    # before the IMEI is even asked for - reuse that cached result here instead of
    # hitting the backend a second time, so this final submit is effectively instant.
    wsn_mismatch_reason = ""
    backend_title = ""
    backend_serial = ""
    if needs_serial_capture:
        if not is_valid_wsn_format(serialized_wsn):
            return jsonify({"status": "error", "message": f"'{serialized_wsn}' doesn't look like a valid WSN (expected format e.g. 24VAR7_X).", "fsn": matched_fsn_for_serial, "is_mobile": is_mobile_item})

        if VERIFY_WSN_SRNO:
            wsn_key = serialized_wsn.strip().upper()
            cache = context.get("wsn_cache", {})
            cached = cache.get(wsn_key)
            if cached and (datetime.now() - cached["ts"]).total_seconds() < WSN_CACHE_TTL_SEC:
                wsn_result = cached["result"]
            else:
                try:
                    wsn_result = verify_wsn_with_backend(serialized_wsn)
                except RuntimeError as e:
                    return jsonify({"status": "error", "message": f"Could not verify WSN against backend ({e}). Please retry the scan.", "fsn": matched_fsn_for_serial, "is_mobile": is_mobile_item})

            backend_title = (wsn_result.get("title") or "").strip()
            backend_serial = (wsn_result.get("serial") or "").strip()
            title_mismatch = bool(backend_title) and backend_title.upper() not in item_name.upper() and item_name.upper() not in backend_title.upper()
            scanned_serials = [s.strip().upper() for s in (serialized_imei1, serialized_imei2) if s.strip()]
            serial_mismatch = bool(backend_serial) and not any(s in backend_serial.upper() for s in scanned_serials)
            if title_mismatch or serial_mismatch:
                wsn_mismatch_reason = "Title" if title_mismatch else "Serial/IMEI"
                safe_csv_export([{
                    "Timestamp": datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                    "Auditor": session.get('ldap_id', 'UNKNOWN'),
                    "Box/Tote ID": context.get("box_id", "UNKNOWN"),
                    "Audit Category": AUDIT_CAT_MAP.get(audit_type, audit_type.upper()),
                    "FSN": matched_fsn_for_serial,
                    "Product": item_name,
                    "WSN": serialized_wsn,
                    "IMEI1": serialized_imei1,
                    "IMEI2": serialized_imei2,
                    "Backend Title": backend_title,
                    "Backend Serial": backend_serial,
                    "Result": "REJECTED",
                    "WSN Mismatch Reason": wsn_mismatch_reason
                }], "serialized_scan_log.csv")
                return jsonify({
                    "status": "error",
                    "message": f"WSN/IMEI mismatch against backend ({wsn_mismatch_reason}) - this unit does not match get_wsn_location records. Please rescan the correct WSN/IMEI.",
                    "fsn": matched_fsn_for_serial,
                    "is_mobile": is_mobile_item
                })

            cache.pop(wsn_key, None)  # accepted - this unit's WSN is consumed, no need to keep it cached
        # else: VERIFY_WSN_SRNO is off - WSN/IMEI are format-checked and captured/logged
        # below as usual, but never checked against the backend, matching the original
        # pre-verification behavior.

    if item_name not in scanned_items:
        scanned_items[item_name] = {
            "count": 0, "expected_qty": expected_qty, 
            "fsn": matched_row.get("FSN", "N/A") if matched_row is not None else "N/A", 
            "wid": matched_row.get("WID", "N/A") if matched_row is not None else "N/A", 
            "type": item_type, "imei": scanned_imei, "imei_mismatched": imei_mismatched,
            "wsn_mismatched": False, "wsn_mismatch_reason": ""
        }
    else:
        if imei_mismatched: scanned_items[item_name]["imei_mismatched"] = True
        if scanned_imei: scanned_items[item_name]["imei"] = scanned_imei

    scanned_items[item_name]["count"] += quantity
    context["scan_history"].append({"type": audit_type, "item_name": item_name, "qty_added": quantity})

    if needs_serial_capture:
        # Accumulate per-unit records (a product can be scanned more than once with
        # different WSN/IMEI per unit) and keep the DB-facing joined strings in sync.
        recs = scanned_items[item_name].setdefault("serialized_records", [])
        recs.append({"wsn": serialized_wsn, "imei1": serialized_imei1, "imei2": serialized_imei2})
        scanned_items[item_name]["wsn"] = "; ".join(r["wsn"] for r in recs)
        scanned_items[item_name]["imei"] = "; ".join(r["imei1"] for r in recs)
        scanned_items[item_name]["imei2"] = "; ".join(r["imei2"] for r in recs if r["imei2"])

        # Dedicated audit-trail CSV, written immediately per unit scanned (in addition
        # to the DB row written later at /finalise). Result=ACCEPTED - any earlier
        # REJECTED rows for this same box/FSN (logged above) stay in this same file,
        # giving the full "what was scanned before the final OK scan" trail.
        safe_csv_export([{
            "Timestamp": datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
            "Auditor": session.get('ldap_id', 'UNKNOWN'),
            "Box/Tote ID": context.get("box_id", "UNKNOWN"),
            "Audit Category": AUDIT_CAT_MAP.get(audit_type, audit_type.upper()),
            "FSN": matched_fsn_for_serial,
            "Product": item_name,
            "WSN": serialized_wsn,
            "IMEI1": serialized_imei1,
            "IMEI2": serialized_imei2,
            "Backend Title": backend_title if needs_serial_capture else "",
            "Backend Serial": backend_serial if needs_serial_capture else "",
            "Result": "ACCEPTED",
            "WSN Mismatch Reason": ""
        }], "serialized_scan_log.csv")

    current_count = scanned_items[item_name]["count"]
    
    if item_type == 'misship': 
        status = "MISSHIP" if audit_type in ['hl_box_audit', 'ob_audit'] else "Excess (A)"
    elif item_type == 'alien': 
        status = "ALIEN" if audit_type in ['hl_box_audit', 'ob_audit'] else ("Excess (A)" if len(scanned_value) == 7 else "ALIEN")
    elif current_count > expected_qty: status = "EXCESS"
    elif current_count < expected_qty: status = "SHORT"
    else: status = "OK"

    matched_fsn = scanned_items[item_name].get("fsn", "N/A")
    if matched_fsn != "N/A" and not df.empty and 'FSN' in df.columns and 'WID' in df.columns:
        fsn_df = df[df['FSN'] == matched_fsn]
        unique_wids = [w for w in fsn_df['WID'].astype(str).unique() if w != 'N/A' and str(w).lower() != 'nan']
        total_parts = len(unique_wids)
        if total_parts > 1:
            scanned_parts = sum(1 for w in unique_wids if any(si.get('fsn') == matched_fsn and si.get('wid') == w and si.get('count', 0) > 0 for si in scanned_items.values()))
            if status == "OK" or status == "SHORT":
                status = f"OK ({scanned_parts}/{total_parts} Parts)"

    if scanned_items[item_name].get("imei_mismatched"):
        status += " (IMEI Mismatch)"
    if scanned_items[item_name].get("wsn_mismatched"):
        status += f" (WSN {scanned_items[item_name].get('wsn_mismatch_reason', '')} Mismatch)"

    fsn_out = scanned_items[item_name].get("fsn", "N/A")

    if audit_type == 'bulk':
        summary = []
        for k, v in scanned_items.items():
            if v['type'] == 'misship': 
                s = "MISSHIP" if audit_type in ['hl_box_audit', 'ob_audit'] else "Excess (A)"
            elif v['type'] == 'alien': 
                s = "ALIEN" if audit_type in ['hl_box_audit', 'ob_audit'] else ("Excess (A)" if len(k) == 7 else "ALIEN")
            elif v['count'] > v['expected_qty']: s = "EXCESS"
            elif v['count'] < v['expected_qty']: s = "SHORT"
            else: s = "OK"
            
            chk_fsn = v.get("fsn", "N/A")
            if chk_fsn != "N/A" and not df.empty and 'FSN' in df.columns and 'WID' in df.columns:
                fsn_df = df[df['FSN'] == chk_fsn]
                unique_wids = [w for w in fsn_df['WID'].astype(str).unique() if w != 'N/A' and str(w).lower() != 'nan']
                total_parts = len(unique_wids)
                if total_parts > 1:
                    scanned_parts = sum(1 for w in unique_wids if any(si.get('fsn') == chk_fsn and si.get('wid') == w and si.get('count', 0) > 0 for si in scanned_items.values()))
                    if s == "OK" or s == "SHORT":
                        s = f"OK ({scanned_parts}/{total_parts} Parts)"

            if v.get("imei_mismatched"): s += " (IMEI Mismatch)"
            if v.get("wsn_mismatched"): s += f" (WSN {v.get('wsn_mismatch_reason', '')} Mismatch)"
            
            summary.append({"EAN": scanned_value, "item_name": k, "Status": s, "Qty": f"{v['count']}/{v['expected_qty']}", "fsn": v.get("fsn", "N/A")})
        return jsonify({"status": "success", "summary": summary})
    
    return jsonify({"status": "success", "ean": scanned_value, "item_name": item_name, "fsn": fsn_out, "match": status, "current_qty_int": current_count, "expected_qty_int": expected_qty, "qty": f"{current_count}/{expected_qty if expected_qty > 0 else 'NA'}", "wsn_mismatched": scanned_items[item_name].get("wsn_mismatched", False), "wsn_mismatch_reason": scanned_items[item_name].get("wsn_mismatch_reason", ""), "wsn": scanned_items[item_name].get("wsn", ""), "imei": scanned_items[item_name].get("imei", ""), "imei2": scanned_items[item_name].get("imei2", "")})

@app.route("/undo_scan", methods=["POST"])
def undo_scan():
    context = get_user_context()
    if not context or not context["scan_history"]: 
        return jsonify({"status": "error", "message": "No scan to undo"}), 400
    
    last = context["scan_history"].pop()
    item = last["item_name"]
    qty_to_remove = last.get("qty_added", 1)
    
    if item in context["scanned_items"]:
        df = context.get("df", pd.DataFrame())
        if context["audit_type"] == 'bulk': 
            del context["scanned_items"][item]
            summary = []
            for k, v in context["scanned_items"].items():
                if v['type'] == 'misship': 
                    s = "MISSHIP" if context["audit_type"] in ['hl_box_audit', 'ob_audit'] else "Excess (A)"
                elif v['type'] == 'alien': 
                    s = "ALIEN" if context["audit_type"] in ['hl_box_audit', 'ob_audit'] else ("Excess (A)" if len(k) == 7 else "ALIEN")
                elif v['count'] > v['expected_qty']: s = "EXCESS"
                elif v['count'] < v['expected_qty']: s = "SHORT"
                else: s = "OK"
                
                chk_fsn = v.get("fsn", "N/A")
                if chk_fsn != "N/A" and not df.empty and 'FSN' in df.columns and 'WID' in df.columns:
                    fsn_df = df[df['FSN'] == chk_fsn]
                    unique_wids = [w for w in fsn_df['WID'].astype(str).unique() if w != 'N/A' and str(w).lower() != 'nan']
                    total_parts = len(unique_wids)
                    if total_parts > 1:
                        scanned_parts = sum(1 for w in unique_wids if any(si.get('fsn') == chk_fsn and si.get('wid') == w and si.get('count', 0) > 0 for si in context["scanned_items"].values()))
                        if s == "OK" or s == "SHORT":
                            s = f"OK ({scanned_parts}/{total_parts} Parts)"

                if v.get("imei_mismatched"): s += " (IMEI Mismatch)"
                summary.append({"EAN": "Reverted", "item_name": k, "Status": s, "Qty": f"{v['count']}/{v['expected_qty']}", "fsn": v.get("fsn", "N/A")})
            return jsonify({"status": "bulk", "message": f"Undone {qty_to_remove} items", "summary": summary})
        else:
            context["scanned_items"][item]["count"] -= qty_to_remove
            new_qty = context["scanned_items"][item]["count"]
            if new_qty <= 0: 
                del context["scanned_items"][item]
                return jsonify({"status": "removed", "undone_ean": item, "message": f"Undone {qty_to_remove} items"})
            else:
                expected = context["scanned_items"][item]["expected_qty"]
                item_type = context["scanned_items"][item].get("type", "normal")
                
                if item_type == 'misship': 
                    status = "MISSHIP" if context["audit_type"] in ['hl_box_audit', 'ob_audit'] else "Excess (A)"
                elif item_type == 'alien': 
                    status = "ALIEN" if context["audit_type"] in ['hl_box_audit', 'ob_audit'] else ("Excess (A)" if len(item) == 7 else "ALIEN")
                elif new_qty > expected: status = "EXCESS"
                elif new_qty < expected: status = "SHORT"
                else: status = "OK"

                matched_fsn = context["scanned_items"][item].get("fsn", "N/A")
                if matched_fsn != "N/A" and not df.empty and 'FSN' in df.columns and 'WID' in df.columns:
                    fsn_df = df[df['FSN'] == matched_fsn]
                    unique_wids = [w for w in fsn_df['WID'].astype(str).unique() if w != 'N/A' and str(w).lower() != 'nan']
                    total_parts = len(unique_wids)
                    if total_parts > 1:
                        scanned_parts = sum(1 for w in unique_wids if any(si.get('fsn') == matched_fsn and si.get('wid') == w and si.get('count', 0) > 0 for si in context["scanned_items"].values()))
                        if status == "OK" or status == "SHORT":
                            status = f"OK ({scanned_parts}/{total_parts} Parts)"

                if context["scanned_items"][item].get("imei_mismatched"): status += " (IMEI Mismatch)"
                
                return jsonify({"status": "updated", "undone_ean": item, "new_qty": f"{new_qty}/{expected if expected > 0 else 'NA'}", "match": status, "message": f"Undone {qty_to_remove} items"})
        
    return jsonify({"status": "error", "message": "Could not undo scan"})

@app.route("/finalise", methods=["POST"])
def finalise():
    context = get_user_context()
    if not context: return jsonify({"status": "error", "message": "Session expired. Please log in again."}), 401

    try:
        df = context.get("df", pd.DataFrame())
        scanned_items = context.get("scanned_items", {})
        box_id = context.get("box_id", "UNKNOWN")
        audit_type = context.get("audit_type", "AUDIT")
        
        bin_status = request.form.get("bin_status", "")
        
        try: damage_data = json.loads(request.form.get("damage_data", "{}"))
        except json.JSONDecodeError: damage_data = {}

        try: expired_data = json.loads(request.form.get("expired_data", "{}"))
        except json.JSONDecodeError: expired_data = {}
        
        try: short_confirmations = json.loads(request.form.get("short_confirmations", "{}"))
        except json.JSONDecodeError: short_confirmations = {}

        expected_items = {str(row['Product']).strip(): row.to_dict() for _, row in df.iterrows()}

        for item_name, confirmed_qty in short_confirmations.items():
            matched_fsn = str(expected_items.get(item_name, {}).get("FSN", "")).strip()
            if is_serialized_fsn(matched_fsn):
                # Serialized products (mobiles/IMEI-tracked) must go through the WSN/
                # IMEI backend-verification flow in /scan_product. This generic
                # short-qty confirmation popup is a loophole otherwise - a free-text
                # qty here bypassed verification entirely. It can now only ever
                # confirm a genuine shortfall against units actually verified, never
                # create or inflate a count for units that were never scanned/checked.
                verified_count = len(scanned_items.get(item_name, {}).get("serialized_records", []))
                if item_name in scanned_items:
                    try:
                        scanned_items[item_name]["count"] = min(int(confirmed_qty), verified_count)
                    except (TypeError, ValueError):
                        pass
                continue

            if item_name not in scanned_items:
                if item_name in expected_items:
                    scanned_items[item_name] = {
                        "count": 0,
                        "expected_qty": int(expected_items[item_name].get("Qty", 0)),
                        "fsn": expected_items[item_name].get("FSN", "N/A"),
                        "wid": expected_items[item_name].get("WID", "N/A"),
                        "type": "normal",
                        "imei_mismatched": False
                    }
            if item_name in scanned_items:
                scanned_items[item_name]["count"] = int(confirmed_qty)

        audit_no = generate_audit_no(audit_type, box_id)
        evidence_file = request.files.get('evidence_image')
        image_name = save_evidence_image(evidence_file, audit_type, audit_no)

        multi_part_fsns = []
        if not df.empty and 'FSN' in df.columns and 'WID' in df.columns:
            fsn_groups = df.groupby('FSN')['WID'].nunique()
            multi_part_fsns = fsn_groups[fsn_groups > 1].index.tolist()

        summary_data = []
        timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        
        for name, details in expected_items.items():
            scan_qty = scanned_items.get(name, {"count": 0})["count"]
            exp_qty = int(details.get("Qty", 0))
            fsn = details.get("FSN", "")
            
            if scan_qty == exp_qty:
                status = "OK"
            elif scan_qty > exp_qty:
                status = "EXCESS"
            else:
                if fsn in multi_part_fsns:
                    status = "Unscanned Part"
                else:
                    status = "SHORT"
            
            scanned_imei = scanned_items.get(name, {}).get("imei", "")
            if scanned_items.get(name, {}).get("imei_mismatched"):
                status += " (IMEI Mismatch)"

            # Map the clean categorical string immediately into Database inserts
            db_category = AUDIT_CAT_MAP.get(audit_type, audit_type.replace('_', ' ').upper())

            summary_data.append({
                "Timestamp": timestamp,
                "Box/Tote ID": box_id, "Product": name, "FSN": fsn, "WID": details.get("WID", "N/A"),
                "Expected Qty": exp_qty, "Scanned Qty": scan_qty, "Status": status, 
                "Audit Category": db_category, "Damage Qty": damage_data.get(name, ""), 
                "Expired Qty": expired_data.get(name, ""), "Bin Status": bin_status,
                "Scanned IMEI": scanned_imei,
                "WSN": scanned_items.get(name, {}).get("wsn", ""),
                "IMEI 2": scanned_items.get(name, {}).get("imei2", ""),
                "Order ID": details.get("Order_ID", "N/A"),
                "Linked Tracking": details.get("Linked_Tracking", "N/A"),
                "Audit No": audit_no, "Image File": image_name, "Auditor": session.get('ldap_id', 'UNKNOWN')
            })

        for name, details in scanned_items.items():
            if name not in expected_items:
                if audit_type in ['hl_box_audit', 'ob_audit']:
                    final_status = "MISSHIP" if details.get('type') == 'misship' else "ALIEN"
                else:
                    final_status = "Excess (A)" if details.get('type') == 'misship' or (details.get('type') == 'alien' and len(name) == 7) else "ALIEN"
                
                scanned_imei = details.get("imei", "")
                if details.get("imei_mismatched"):
                    final_status += " (IMEI Mismatch)"

                db_category = AUDIT_CAT_MAP.get(audit_type, audit_type.replace('_', ' ').upper())

                summary_data.append({
                    "Timestamp": timestamp,
                    "Box/Tote ID": box_id, "Product": name, "FSN": details.get("fsn", "N/A"), "WID": details.get("wid", "N/A"),
                    "Expected Qty": 0, "Scanned Qty": details["count"], "Status": final_status, 
                    "Audit Category": db_category, "Damage Qty": damage_data.get(name, ""), 
                    "Expired Qty": expired_data.get(name, ""), "Bin Status": bin_status,
                    "Scanned IMEI": scanned_imei,
                    "WSN": details.get("wsn", ""),
                    "IMEI 2": details.get("imei2", ""),
                    "Order ID": "N/A", "Linked Tracking": "N/A",
                    "Audit No": audit_no, "Image File": image_name, "Auditor": session.get('ldap_id', 'UNKNOWN')
                })

        with db_lock:
            conn = get_db_connection()
            try:
                for row in summary_data:
                    conn.execute('''
                        INSERT INTO master_audit_log ("Timestamp", "LDAP ID", "Warehouse", "Audit Category", "Box/Tote ID", "FSN", "WID", "Product", "Status", "Scanned Qty", "Expected Qty", "Damage Qty", "Expired Qty", "Bin Status", "Scanned IMEI", "WSN", "IMEI 2", "Order ID", "Linked Tracking", "Audit No", "Image File")
                        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    ''', (timestamp, row['Auditor'], session.get('warehouse_id'), row['Audit Category'], row['Box/Tote ID'], row['FSN'], row['WID'], row['Product'], row['Status'], row['Scanned Qty'], row['Expected Qty'], row['Damage Qty'], row['Expired Qty'], row['Bin Status'], row['Scanned IMEI'], row.get('WSN', ''), row.get('IMEI 2', ''), row['Order ID'], row['Linked Tracking'], row['Audit No'], row['Image File']))
                conn.commit()
            finally:
                conn.close()

        context["latest_summary"] = summary_data
        context["latest_audit_no"] = audit_no
        return jsonify({"status": "success", "message": "Finalised! Please review summary.", "redirect_url": url_for("get_summary")})
    except Exception as e:
        print(f"Finalise Exception: {e}")
        return jsonify({"status": "error", "message": f"Server crash during submission. Details: {e}"}), 500

@app.route("/api/export_csv", methods=["POST"])
def export_csv():
    context = get_user_context()
    if not context: return jsonify({"status": "error", "message": "Session expired."}), 401
    
    audit_type = context.get("audit_type", "AUDIT")
    audit_no = context.get("latest_audit_no", "")
    category = AUDIT_CAT_MAP.get(audit_type, audit_type.replace('_', ' ').upper())

    if not audit_no:
        return jsonify({"status": "error", "message": "No data found for today's audits."}), 400
    
    try:
        conn = get_db_connection()
        # Scoped to the exact Audit No just finalized (unique per finalise() call) -
        # NOT "today's whole category" like before. That old query re-fetched every
        # earlier box's rows too, which was safe only because the old code OVERWROTE
        # the file each time. Since these two files now APPEND and accumulate into
        # "the whole db" over time, scoping to just the new Audit No is what prevents
        # every earlier box being re-appended (duplicated) on every subsequent export.
        df = pd.read_sql_query('SELECT * FROM master_audit_log WHERE "Audit No" = ?', conn, params=[audit_no])
        conn.close()
        
        if df.empty:
            return jsonify({"status": "error", "message": "No data found for today's audits."}), 400
            
        if 'id' in df.columns: df = df.drop(columns=['id'])

        # --- RAW export: whole-db cumulative, new data appended each export ---
        raw_file = f"{audit_type}_raw.csv"
        raw_path = os.path.join(CSV_DIR, raw_file)
        try:
            df.to_csv(raw_path, mode='a', header=not os.path.exists(raw_path), index=False)
        except PermissionError:
            backup_path = os.path.join(CSV_DIR, f"{audit_type}_raw_{int(time.time())}.csv")
            df.to_csv(backup_path, mode='a', header=not os.path.exists(backup_path), index=False)

        # --- CQ export: whole-db cumulative, new data appended each export ---
        cq_input = df.copy()
        if category in ['CUSTOMER OUTBOUND AUDIT', 'NCOB BOX AUDIT']:
            cq_input = consolidate_ob_audits(cq_input)
        cq_df = generate_cq_report(cq_input)

        cq_file = f"{audit_type}_cq_format.csv"
        cq_path = os.path.join(CSV_DIR, cq_file)
        try:
            cq_df.to_csv(cq_path, mode='a', header=not os.path.exists(cq_path), index=False)
        except PermissionError:
            backup_path = os.path.join(CSV_DIR, f"{audit_type}_cq_format_{int(time.time())}.csv")
            cq_df.to_csv(backup_path, mode='a', header=not os.path.exists(backup_path), index=False)
        
        context["latest_summary"] = []
        context["latest_audit_no"] = ""
        return jsonify({"status": "success", "message": "Detailed report exported successfully."})
        
    except Exception as e:
        print(f"Export CSV Error: {e}")
        return jsonify({"status": "error", "message": f"Export Failed: {e}"}), 500

@app.route("/summary")
def get_summary():
    context = get_user_context()
    if not context: return redirect(url_for("login"))
    summary = context.get("latest_summary", [])
    if not summary: return redirect(url_for("landing"))
    
    audit_slug = context.get("audit_type", "unit")
    total_expected = sum(int(row.get("Expected Qty", 0) or 0) for row in summary)
    total_scanned = sum(int(row.get("Scanned Qty", 0) or 0) for row in summary)
    meta = {
        "box_id": summary[0].get("Box/Tote ID", "N/A"), 
        "audit_type": summary[0].get("Audit Category", "AUDIT").upper(), 
        "audit_no": summary[0].get("Audit No", "N/A"),
        "audit_slug": audit_slug,
        "total_expected": total_expected,
        "total_scanned": total_scanned
    }
    return render_template("summary.html", meta=meta, summary=summary)

@app.route("/history_page")
def history_page():
    if 'ldap_id' not in session: return redirect(url_for("login"))
    return render_template("history.html")
# ─────────────────────────────────────────────────────────────────────────────
# PASTE THIS BLOCK right after the /history_page route (after line 2102)
# ─────────────────────────────────────────────────────────────────────────────

@app.route("/api/box_search", methods=["GET"])
def box_search():
    """Search master_audit_log by Box/Tote ID (exact-first, then LIKE fallback)."""
    if 'ldap_id' not in session:
        return jsonify({"status": "error", "message": "Not authenticated"}), 401

    box_id = request.args.get("box_id", "").strip()
    if not box_id:
        return jsonify({"status": "error", "message": "No Box ID provided"}), 400

    # Columns we want to surface in the UI
    COLS = [
        "Timestamp", "LDAP ID", "Warehouse", "Audit Category",
        "Box/Tote ID", "WID", "FSN", "Product",
        "Expected Qty", "Scanned Qty", "Status",
        "WSN", "Scanned IMEI", "IMEI 2",
        "Damage Qty", "Audit No", "Order ID", "Issue", "Sub Issue"
    ]
    select_cols = ", ".join(f'"{c}"' for c in COLS)

    try:
        conn = get_db_connection()
        try:
            # 1) Exact match first
            rows = conn.execute(
                f'SELECT {select_cols} FROM master_audit_log '
                f'WHERE "Box/Tote ID" = ? ORDER BY "Timestamp" DESC LIMIT 200',
                (box_id,)
            ).fetchall()

            # 2) Fallback: case-insensitive partial match if nothing found
            if not rows:
                rows = conn.execute(
                    f'SELECT {select_cols} FROM master_audit_log '
                    f'WHERE LOWER("Box/Tote ID") LIKE ? ORDER BY "Timestamp" DESC LIMIT 200',
                    (f"%{box_id.lower()}%",)
                ).fetchall()
        finally:
            conn.close()

        records = [dict(r) for r in rows]
        return jsonify({
            "status": "ok",
            "count": len(records),
            "box_id": box_id,
            "records": records
        })

    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500
    
@app.route("/api/download_history", methods=["POST"])
def download_history():
    start_date = request.form.get("start_date")
    end_date = request.form.get("end_date")
    audit_type = request.form.get("audit_type")
    report_format = request.form.get("report_format")
    
    if not start_date or not end_date:
        flash("Start and End dates are required.", "flash-danger")
        return redirect(url_for("history_page"))
        
    try:
        query = 'SELECT * FROM master_audit_log WHERE "Timestamp" >= ? AND "Timestamp" <= ?'
        params = [f"{start_date} 00:00:00", f"{end_date} 23:59:59"]
        
        if audit_type and audit_type != "ALL":
            categories_to_query = get_db_categories(audit_type)
            placeholders = ",".join(["?"] * len(categories_to_query))
            query += f' AND "Audit Category" IN ({placeholders})'
            params.extend(categories_to_query)
            
        conn = get_db_connection()
        try:
            df = pd.read_sql_query(query, conn, params=params)
        finally:
            conn.close()
        
        if df.empty:
            flash("No records found for the selected range.", "flash-danger")
            return redirect(url_for("history_page"))
            
        if 'id' in df.columns: 
            df = df.drop(columns=['id'])

        # --- Check if we need to generate the Custom NCOB XLSX Report ---
        if audit_type == "NCOB BOX AUDIT" and report_format != "CQ":
            # Clean numeric columns
            df['Expected Qty'] = pd.to_numeric(df['Expected Qty'], errors='coerce').fillna(0)
            df['Scanned Qty'] = pd.to_numeric(df['Scanned Qty'], errors='coerce').fillna(0)
            df['Damage Qty'] = pd.to_numeric(df['Damage Qty'], errors='coerce').fillna(0)

            # Helper for MULTIPLE strings
            def get_multiple(series):
                unique_vals = series.dropna().unique()
                if len(unique_vals) > 1: return "MULTIPLE"
                elif len(unique_vals) == 1: return unique_vals[0]
                else: return np.nan

            # Helper: a box's distinct issue categories, in PRIORITY order
            #   Missing (SHORT) > Misshipment (MISSHIP/ALIEN) > Excess > Damage
            def get_box_issues(group):
                statuses = [str(s).upper() for s in group['Status'].dropna()]
                present = []
                if any('SHORT' in s or 'UNSCANNED' in s for s in statuses):
                    present.append('Missing')
                if any('MISSHIP' in s or 'ALIEN' in s for s in statuses):
                    present.append('Misshipment')
                if any('EXCESS' in s for s in statuses):
                    present.append('Excess')
                if group['Damage Qty'].sum() > 0:
                    present.append('Damage')
                return present

            # Grouping and summarizing the NCOB Data
            summary = df.groupby('Box/Tote ID', as_index=False).agg(
                Timestamp=('Timestamp', 'first'),
                LDAP_ID=('LDAP ID', 'first'),
                Audit_Category=('Audit Category', 'first'),
                WID=('WID', 'first'),
                FSN=('FSN', get_multiple),
                Product=('Product', get_multiple),
                Expected_Qty=('Expected Qty', 'sum'),
                Scanned_Qty=('Scanned Qty', 'sum'),
                Status=('Status', get_multiple),
                Audit_No=('Audit No', 'first')
            )

            # Standardize names
            summary = summary.rename(columns={
                'LDAP_ID': 'LDAP ID',
                'Audit_Category': 'Audit Category',
                'Expected_Qty': 'Expected Qty',
                'Scanned_Qty': 'Scanned Qty',
                'Audit_No': 'Audit No'
            })

            # Calculate Damage Qty sum natively
            summary['Damage Qty'] = df.groupby('Box/Tote ID')['Damage Qty'].sum().values
            
            # Issue Qty = GROSS discrepancy on issue items (short + excess + misship),
            # summed per box. The old net |Expected-Scanned| hid issues when a short
            # and a misship cancelled out (e.g. box BCRI2DMCR: 1 short + 1 misship
            # netted to 0). Gross reflects the real per-box issue quantity.
            _iq = (df['Expected Qty'] - df['Scanned Qty']).abs()
            _sl = df['Status'].astype(str).str.strip().str.lower()
            _issue_mask = (_sl.str.contains('short',   na=False) |
                           _sl.str.contains('excess',  na=False) |
                           _sl.str.contains('misship', na=False) |
                           _sl.str.contains('alien',   na=False))
            _iq_by_box = (_iq * _issue_mask).groupby(df['Box/Tote ID']).sum()
            summary['Issue Qty'] = summary['Box/Tote ID'].map(_iq_by_box).fillna(0).astype(int)

            # Issues = every category (priority order); FINAL STATUS = top priority only
            issues_df = df.groupby('Box/Tote ID').apply(get_box_issues).reset_index(name='_issues')
            issues_df['Issues'] = issues_df['_issues'].apply(lambda lst: "-".join(lst) if lst else "OK")
            issues_df['FINAL STATUS'] = issues_df['_issues'].apply(lambda lst: lst[0] if lst else "OK")
            issues_df = issues_df.drop(columns='_issues')
            summary = pd.merge(summary, issues_df, on='Box/Tote ID')

            # Reorder Summary columns cleanly
            target_cols = [
                'Timestamp', 'LDAP ID', 'Audit Category', 'Box/Tote ID', 'WID', 'FSN',
                'Product', 'Expected Qty', 'Scanned Qty', 'Issue Qty', 'Status', 'Damage Qty',
                'Audit No', 'Issues', 'FINAL STATUS'
            ]
            summary = summary[[c for c in target_cols if c in summary.columns]]

            # Output to an in-memory XLSX file
            output = io.BytesIO()
            with pd.ExcelWriter(output, engine='openpyxl') as writer:
                df.to_excel(writer, sheet_name='Raw Data', index=False)
                summary.to_excel(writer, sheet_name='Summary', index=False)
                
            output.seek(0)
            
            filename = f"Audit_History_{start_date}to{end_date}_NCOB_Processed.xlsx"
            return send_file(
                output, 
                as_attachment=True, 
                download_name=filename,
                mimetype='application/vnd.openxmlformats-officedocument.spreadsheetml.sheet'
            )

        # --- Standard Logic for Other Formats ---
        if audit_type == "CUSTOMER OUTBOUND AUDIT" or audit_type == "ALL":
            ob_mask = df['Audit Category'] == 'CUSTOMER OUTBOUND AUDIT'
            if ob_mask.any():
                df_ob = consolidate_ob_audits(df[ob_mask])
                df_other = df[~ob_mask]
                df = pd.concat([df_other, df_ob], ignore_index=True)
                df = df.sort_values('Timestamp', ascending=False)
        
        if report_format == "CQ":
            df = generate_cq_report(df)
            ordered_cols = df.columns.tolist() 
        else:
            ordered_cols = ['Timestamp', 'LDAP ID', 'Warehouse', 'Audit Category', 'Box/Tote ID', 'Order ID', 'Linked Tracking', 'WID', 'FSN', 'Product', 'Expected Qty', 'Scanned Qty', 'Status', 'Damage Qty', 'Expired Qty', 'Bin Status', 'Scanned IMEI', 'WSN', 'IMEI 2', 'PV Status', 'Issue', 'Sub Issue', 'Return Reason', 'Audit No', 'Image File']
            final_cols = [c for c in ordered_cols if c in df.columns] + [c for c in df.columns if c not in ordered_cols]
            df = df[final_cols]
        
        csv_data = df.to_csv(index=False)
        
        return Response(
            csv_data,
            mimetype="text/csv",
            headers={"Content-disposition": f"attachment; filename=Audit_History_{start_date}to{end_date}_{report_format}.csv"}
        )
    except Exception as e:
        flash(f"Error fetching history: {e}", "flash-danger")
        return redirect(url_for("history_page"))

@app.route("/quit")
def quit_session():
    ldap_id = None
    with sessions_lock:
        user_id = session.pop('user_id', None)
        if user_id and user_id in user_sessions:
            ldap_id = user_sessions[user_id].get('ldap_id')
            try: user_sessions[user_id]['driver'].quit()
            except Exception: pass
            del user_sessions[user_id]

    if ldap_id:
        leave_ncob_pool(ldap_id)

    session.clear()
    flash("You have been securely logged out.", "flash-info")
    return redirect(url_for("login"))

def session_reaper():
    while True:
        time.sleep(300)
        stale_ldap_ids = []
        with sessions_lock:
            cutoff = datetime.now() - timedelta(minutes=SESSION_TIMEOUT_MINUTES)
            stale = [uid for uid, ctx in user_sessions.items() if ctx.get("last_seen", datetime.now()) < cutoff]
            for uid in stale:
                stale_ldap_ids.append(user_sessions[uid].get('ldap_id'))
                try: user_sessions[uid]['driver'].quit()
                except Exception: pass
                del user_sessions[uid]
        for ldap_id in stale_ldap_ids:
            if ldap_id:
                leave_ncob_pool(ldap_id)

if __name__ == "__main__":
    init_db()
    load_audit_rules()
    threading.Thread(target=session_reaper, daemon=True).start()
    threading.Thread(target=ncob_snapshot_cleaner, daemon=True).start()
    
    app.run(host="0.0.0.0", port=7900, debug=False, use_reloader=False, threaded=True)