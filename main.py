import os
import io
import re
import json
import random
import shutil
import asyncio
import zipfile
import traceback
import xml.etree.ElementTree as ET
import time
import logging
from pathlib import Path
from typing import List, Dict, Any, Optional, Tuple

import pandas as pd
from aiogram import Bot, Dispatcher, F
from aiogram.types import Message, FSInputFile, ReplyKeyboardMarkup, KeyboardButton, ReplyKeyboardRemove
from aiogram.filters import CommandStart
from aiogram.fsm.state import StatesGroup, State
from aiogram.fsm.context import FSMContext
from dotenv import load_dotenv
import csv

from playwright.async_api import async_playwright
import aiohttp

# ---------------- CONFIG ----------------
load_dotenv()
TOKEN = os.getenv("BOT_TOKEN")  # из .env

API_BASE  = "https://idsdatahubdashboardapi.azurewebsites.net"
URL       = "https://datahubdashboard.idsnext.live"
MENU_ITEM = "Bookings from Channels to (FN & FX)"

# Параллельность
PMS_CONCURRENCY       = 16   # параллельных PMS
TOKEN_CONCURRENCY     = 160  # параллельных запросов XML (токенов)

# HTTP лимиты/ретраи
REQ_TIMEOUT_MS    = 60_000
RETRY_ATTEMPTS    = 3
RETRY_BASE_DELAY  = 0.5
RETRY_JITTER      = 0.3

BOOKLOG_TIMEOUT_MS     = 120_000
BOOKLOG_RETRY_ATTEMPTS = 5
BOOKLOG_JITTER         = 0.6
BOOKLOG_BASE_DELAY     = 0.8

# Писатели
WRITERS = 8
WRITE_QUEUE_MAXSIZE = 10_000

DEFAULT_CM_CODE = "CM1000"
WORK_ROOT = Path("work_runs")
WORK_ROOT.mkdir(exist_ok=True)
OLD_XML_DIR = Path("xml_api")  # из старых запусков — будем чистить

SAFE_CHARS = re.compile(r'[\\/*?:"<>|]+')
TEST_ONLY_PMS = None  # например, 7

# ======= доп. фильтр доменов для "все остальные почты" =======
EXCLUDE_EMAIL_DOMAINS = {
    "@m.expediapartnercentral.com",
    "@agoda-messaging.com",
    "@guest.booking.com",
    "@makemytrip.com",
    "@cleartrip.com",
    "@easemytrip.com",
    "@hotelpartner@ixigo.com",
    "@travelplusapp.com",
    "@agoda.com",
    "@tbo.com",
    "@ixigo.com",
    "@grnconnect.com",
    "@galaxytravellers.com",
    "@guest.trip.com",
    "@riya.travel"
}

# ---------------- LOGGER ----------------
logger = logging.getLogger("dhbot")

def log_duration(tag: str, start: float, extra: str = ""):
    elapsed = time.perf_counter() - start
    logger.info(f"[TIMER] {tag} | {elapsed:.3f}s {extra}".strip())

# ---------------- FSM ----------------
class AuthFlow(StatesGroup):
    waiting_username   = State()
    waiting_password   = State()
    waiting_dates      = State()
    waiting_choice     = State()   # номера или почты
    waiting_email_kind = State()   # если почты: booking / other
    waiting_numbers_fmt = State()

KB_NUMBERS_FMT = ReplyKeyboardMarkup(
    keyboard=[
        [KeyboardButton(text="Word")],
        [KeyboardButton(text="Kadir")]
    ],
    resize_keyboard=True
)

# Кнопки
KB_PARSE_CHOICE = ReplyKeyboardMarkup(
    keyboard=[
        [KeyboardButton(text="📞 Спарсить только номера")],
        [KeyboardButton(text="✉️ Спарсить только почты")]
    ],
    resize_keyboard=True
)

KB_EMAIL_KIND = ReplyKeyboardMarkup(
    keyboard=[
        [KeyboardButton(text="Booking почты")],
        [KeyboardButton(text="Все остальные почты")]
    ],
    resize_keyboard=True
)


# ---------------- UTILS ----------------
def safe_filename(s: str) -> str:
    return SAFE_CHARS.sub("_", s).strip() or "file"

def extract_pms_from_label(label: str) -> Optional[int]:
    head = label.split("-", 1)[0].strip()
    try:
        return int(head)
    except Exception:
        return None

async def send_error(m: Message, where: str, exc: Exception):
    tb = "".join(traceback.format_exception_only(type(exc), exc)).strip()
    msg = f"❌ Ошибка на шаге *{where}*: `{tb}`"
    logger.exception(f"[ERROR] {where}: {exc}")
    if len(msg) > 3500:
        msg = msg[:3490] + "…`"
    await m.answer(msg, parse_mode="Markdown")

def safe_rmtree(path: Path):
    try:
        if path.exists():
            shutil.rmtree(path, ignore_errors=True)
            logger.info(f"[CLEANUP] Removed directory: {path}")
    except Exception as e:
        logger.warning(f"[CLEANUP] Failed to remove {path}: {e}")

def _kadir_row_from_xml(xml_text: str) -> Optional[dict]:
    if not xml_text or not is_booking_com_xml(xml_text):
        return None

    try:
        root = ET.fromstring(xml_text)
    except Exception:
        try:
            xml_text = re.sub(r'^\s*[^<]+<', '<', xml_text, count=1)
            root = ET.fromstring(xml_text)
        except Exception:
            return None

    ns = {
        "ota": "http://www.opentravel.org/OTA/2003/05",
        "soap": "http://www.w3.org/2003/05/soap-envelope",
    }
    def t(el) -> str:
        return (el.text or "").strip() if el is not None and el.text else ""

    given   = t(root.find(".//ota:GivenName", ns))
    surname = t(root.find(".//ota:Surname", ns))

    ts = root.find(".//ota:TimeSpan", ns)
    ts_start = ts.attrib.get("Start", "") if ts is not None else ""
    ts_end   = ts.attrib.get("End",   "") if ts is not None else ""

    tot = root.find(".//ota:Total", ns)
    a_inc   = (tot.attrib.get("AmountIncludingMarkup", "") if tot is not None else "").strip()
    cur     = (tot.attrib.get("CurrencyCode", "")          if tot is not None else "").strip()
    total_s = f"{a_inc} {cur}".strip()

    email = t(root.find(".//ota:Email", ns))

    tel = root.find(".//ota:Telephone", ns)
    phone = (tel.attrib.get("PhoneNumber", "") if tel is not None else "").strip()

    bpi = root.find(".//ota:BasicPropertyInfo", ns)
    chain = (bpi.attrib.get("ChainCode", "") if bpi is not None else "").strip()

    # адрес — возьмём первую строку AddressLine, если есть
    addr = "Your reservation not confirmed"

    return {
        "GivenName": given,
        "Surname": surname,
        "TimeSpan_start": ts_start,
        "TimeSpan_end": ts_end,
        "Total_inc_currency": total_s,
        "Email": email,
        "Telephone": phone,
        "BasicPropertyInfo_ChainCode": chain,
        "Address": addr,
    }



def write_kadir_csv(hotel_name: str, rows: list[dict], out_dir: Path) -> Path:
    """
    CSV в формате столбцов:
    Номер;GivenName;Surname;TimeSpan start;TimeSpan End;
    Total AmountIncludingMarkup + CurrencyCode;Email;Telephone PhoneNumber;
    BasicPropertyInfo ChainCode;Address
    """
    out_dir.mkdir(parents=True, exist_ok=True)
    fn = safe_filename(hotel_name) + ".csv"
    path = out_dir / fn

    headers = [
        "Номер",
        "GivenName",
        "Surname",
        "TimeSpan start",
        "TimeSpan End",
        "Total AmountIncludingMarkup + CurrencyCode",
        "Email",
        "Telephone PhoneNumber",
        "BasicPropertyInfo ChainCode",
        "Address",
    ]
    # utf-8-sig => Excel корректно понимает кириллицу
    with path.open("w", encoding="utf-8-sig", newline="") as f:
        w = csv.writer(f, delimiter=';', quoting=csv.QUOTE_MINIMAL)
        w.writerow(headers)
        for idx, r in enumerate(rows, start=1):
            w.writerow([
                idx,
                r.get("GivenName", ""),
                r.get("Surname", ""),
                r.get("TimeSpan_start", ""),
                r.get("TimeSpan_end", ""),
                r.get("Total_inc_currency", ""),
                r.get("Email", ""),
                r.get("Telephone", ""),
                r.get("BasicPropertyInfo_ChainCode", ""),
                r.get("Address", ""),
            ])

    logger.info(f"[REPORT] Wrote KADIR CSV for hotel '{hotel_name}' with {len(rows)} rows -> {path}")
    return path



def build_kadir_reports(pms_to_name: dict[int, str], run_dir: Path) -> Tuple[List[Path], int]:
    out_paths, total_rows = [], 0
    save_dir = run_dir / "xml"
    out_dir  = run_dir / "reports"
    out_dir.mkdir(exist_ok=True, parents=True)

    for pms, hotel_name in pms_to_name.items():
        pms_dir = save_dir / str(pms)
        if not pms_dir.exists():
            continue
        rows = []
        for xml_path in sorted(pms_dir.glob("*.xml")):
            try:
                xml_text = xml_path.read_text(encoding="utf-8", errors="ignore")
                row = _kadir_row_from_xml(xml_text)
                if row:
                    rows.append(row)
            except Exception:
                pass
        if rows:
            total_rows += len(rows)
            out_paths.append(write_kadir_csv(hotel_name, rows, out_dir))

    return out_paths, total_rows

def build_kadir_merged(pms_to_name: dict[int, str], run_dir: Path) -> Tuple[List[Path], int]:
    """
    Собираем все строки в ОДИН CSV-файл (для режима Kadir).
    Возвращаем ([путь_к_csv], всего_строк).
    Требует, чтобы _kadir_row_from_xml возвращал поля:
    GivenName, Surname, TimeSpan_start, TimeSpan_end, Total_inc_currency,
    Email, Telephone, BasicPropertyInfo_ChainCode, Address
    """
    out_dir = run_dir / "reports"
    out_dir.mkdir(exist_ok=True, parents=True)
    out_path = out_dir / "kadir_all.csv"

    headers = [
        "Номер",
        "GivenName",
        "Surname",
        "TimeSpan start",
        "TimeSpan End",
        "Total AmountIncludingMarkup + CurrencyCode",
        "Email",
        "Telephone PhoneNumber",
        "BasicPropertyInfo ChainCode",
        "Address",
    ]

    total = 0
    with out_path.open("w", encoding="utf-8-sig", newline="") as f:
        w = csv.writer(f, delimiter=';', quoting=csv.QUOTE_MINIMAL)
        w.writerow(headers)

        idx = 1
        save_dir = run_dir / "xml"
        # идём по PMS в предсказуемом порядке
        for pms in sorted(pms_to_name.keys()):
            pms_dir = save_dir / str(pms)
            if not pms_dir.exists():
                continue
            for xml_path in sorted(pms_dir.glob("*.xml")):
                try:
                    xml_text = xml_path.read_text(encoding="utf-8", errors="ignore")
                    row = _kadir_row_from_xml(xml_text)
                    if not row:
                        continue
                    w.writerow([
                        idx,
                        row.get("GivenName", ""),
                        row.get("Surname", ""),
                        row.get("TimeSpan_start", ""),
                        row.get("TimeSpan_end", ""),
                        row.get("Total_inc_currency", ""),
                        row.get("Email", ""),
                        row.get("Telephone", ""),
                        row.get("BasicPropertyInfo_ChainCode", ""),
                        row.get("Address", ""),
                    ])
                    idx += 1
                    total += 1
                except Exception as e:
                    logger.warning(f"[KADIR MERGE] Failed on {xml_path}: {e}")

    logger.info(f"[REPORT] Wrote merged KADIR CSV with {total} rows -> {out_path}")
    return [out_path], total





# ========= ПАРСИНГ XML =========
def parse_booking_info(xml_text: str) -> dict:
    """
    Парсим Arrival(Start) / Departure(End) / GivenName / Surname / Phone / Email / TotalAmount / Currency из XML.
    Если чего-то нет — пустая строка.
    """
    if not xml_text:
        return {}
    try:
        root = ET.fromstring(xml_text)
    except Exception:
        try:
            xml_text = re.sub(r'^\s*[^<]+<', '<', xml_text, count=1)
            root = ET.fromstring(xml_text)
        except Exception:
            return {}

    ns = {
        "ota": "http://www.opentravel.org/OTA/2003/05",
        "soap": "http://www.w3.org/2003/05/soap-envelope",
    }

    def findtext(path: str) -> str:
        el = root.find(path, ns)
        return (el.text or "").strip() if el is not None and el.text else ""

    ts = root.find(".//ota:TimeSpan", ns)
    start = (ts.attrib.get("Start", "") if ts is not None else "").strip()
    end   = (ts.attrib.get("End",   "") if ts is not None else "").strip()

    given   = findtext(".//ota:GivenName")
    surname = findtext(".//ota:Surname")
    email   = findtext(".//ota:Email")

    phone = ""
    ph_el = root.find(".//ota:Telephone", ns)
    if ph_el is not None:
        phone = (ph_el.attrib.get("PhoneNumber", "") or "").strip()

    total_amount = ""
    currency = ""
    total_el = root.find(".//ota:Total", ns)
    if total_el is not None and isinstance(total_el.attrib, dict):
        currency = (total_el.attrib.get("CurrencyCode") or "").strip()
        for k in ("AmountIncludingMarkup", "AmountAfterTax", "AmountBeforeTax"):
            v = total_el.attrib.get(k)
            if v:
                total_amount = str(v).strip()
                break

    return {
        "start":   start,
        "end":     end,
        "given":   given,
        "surname": surname,
        "phone":   phone,
        "email":   email,
        "total":   total_amount,
        "currency": currency,
    }

def is_booking_com_xml(xml_text: str) -> bool:
    """
    Возвращает True, если XML относится к Booking.com.
    """
    if not xml_text:
        return False

    try:
        root = ET.fromstring(xml_text)
    except Exception:
        try:
            xml_text = re.sub(r'^\s*[^<]+<', '<', xml_text, count=1)
            root = ET.fromstring(xml_text)
        except Exception:
            return False

    ns = {
        "ota": "http://www.opentravel.org/OTA/2003/05",
        "soap": "http://www.w3.org/2003/05/soap-envelope",
    }

    comp = root.find(".//ota:Source/ota:BookingChannel/ota:CompanyName", ns)
    if comp is None:
        return False

    code = (comp.attrib.get("Code") or "").strip()
    if code == "19":
        return True

    text = (comp.text or "").strip().lower()
    if "booking.com" in text:
        return True

    return False


# ---------- TXT отчёты ----------
def write_hotel_txt(hotel_name: str, rows: list[dict], out_dir: Path) -> Path:
    out_dir.mkdir(parents=True, exist_ok=True)
    fn = safe_filename(hotel_name) + ".txt"
    path = out_dir / fn

    with path.open("w", encoding="utf-8", newline="") as f:
        for r in rows:
            arrival  = r.get("start", "")
            depart   = r.get("end", "")
            name = f"{(r.get('given') or '').strip()} {(r.get('surname') or '').strip()}".strip()
            phone    = r.get("phone", "")
            amount   = r.get("total", "")
            curr     = r.get("currency", "")
            price    = (amount + (" " + curr if curr else "")).strip()
            line = f"{hotel_name}|{arrival}|{depart}|{name}|{phone}|{price}"
            f.write(line + "\n")
    logger.info(f"[REPORT] Wrote numbers TXT for hotel '{hotel_name}' with {len(rows)} rows -> {path}")
    return path

def write_hotel_emails_txt(hotel_name: str, rows: list[dict], out_dir: Path) -> Path:
    """
    TXT для почт: Hotel|Arrival|Departure|Name|Email|Phone|TotalAmount Currency
    Формат полностью как в отчёте по телефонам, только добавлен Email.
    """
    out_dir.mkdir(parents=True, exist_ok=True)
    fn = safe_filename(hotel_name) + ".txt"
    path = out_dir / fn

    with path.open("w", encoding="utf-8", newline="") as f:
        for r in rows:
            arrival  = (r.get("start") or "").strip()
            depart   = (r.get("end") or "").strip()
            name     = f"{(r.get('given') or '').strip()} {(r.get('surname') or '').strip()}".strip()
            email    = (r.get("email") or "").strip()
            phone    = (r.get("phone") or "").strip()
            amount   = (r.get("total") or "").strip()
            curr     = (r.get("currency") or "").strip()

            # цена в том же виде, что и в write_hotel_txt
            price = (amount + (" " + curr if curr else "")).strip()

            # окончательная строка
            line = f"{hotel_name}|{arrival}|{depart}|{name}|{email}|{phone}|{price}"
            f.write(line + "\n")

    logger.info(f"[REPORT] Wrote emails TXT for hotel '{hotel_name}' with {len(rows)} rows -> {path}")
    return path



def build_hotel_reports(pms_to_name: dict[int, str], run_dir: Path) -> Tuple[List[Path], int, int]:
    t0 = time.perf_counter()
    out_paths = []
    save_dir = run_dir / "xml"
    report_dir = run_dir / "reports"
    report_dir.mkdir(exist_ok=True, parents=True)

    total_rows = 0
    total_emails = 0
    logger.info(f"[BUILD_REPORTS] Start numbers (Booking-only). Hotels={len(pms_to_name)}")

    for pms, hotel_name in pms_to_name.items():
        t1 = time.perf_counter()
        pms_dir = save_dir / str(pms)
        if not pms_dir.exists():
            logger.info(f"[BUILD_REPORTS] No XML directory for PMS={pms}")
            continue
        rows = []
        count_xml = 0
        for xml_path in sorted(pms_dir.glob("*.xml")):
            count_xml += 1
            try:
                xml_text = xml_path.read_text(encoding="utf-8", errors="ignore")
                if not is_booking_com_xml(xml_text):
                    continue
                row = parse_booking_info(xml_text)
                if any((row.get("start"), row.get("end"), row.get("given"), row.get("surname"),
                        row.get("phone"), row.get("email"), row.get("total"))):
                    rows.append(row)
            except Exception as e:
                logger.warning(f"[BUILD_REPORTS] Failed parse XML {xml_path}: {e}")

        if rows:
            total_rows += len(rows)
            total_emails += sum(1 for r in rows if (r.get("email") or "").strip())
            out = write_hotel_txt(hotel_name, rows, report_dir)
            out_paths.append(out)
        log_duration("BUILD_REPORTS per PMS", t1, f"(PMS={pms}, files={count_xml}, rows_kept={len(rows)})")

    log_duration("BUILD_REPORTS total", t0, f"(TXT files={len(out_paths)}, rows={total_rows}, emails={total_emails})")
    return out_paths, total_rows, total_emails


def build_email_reports(pms_to_name: dict[int, str], run_dir: Path, email_kind: str) -> Tuple[List[Path], int]:
    t0 = time.perf_counter()
    out_paths = []
    save_dir = run_dir / "xml"
    report_dir = run_dir / "reports"
    report_dir.mkdir(exist_ok=True, parents=True)

    total_emails = 0
    logger.info(f"[BUILD_EMAILS] Start emails (kind={email_kind}). Hotels={len(pms_to_name)}")

    for pms, hotel_name in pms_to_name.items():
        t1 = time.perf_counter()
        pms_dir = save_dir / str(pms)
        if not pms_dir.exists():
            logger.info(f"[BUILD_EMAILS] No XML directory for PMS={pms}")
            continue

        rows = []
        count_xml = 0
        kept = 0
        for xml_path in sorted(pms_dir.glob("*.xml")):
            count_xml += 1
            try:
                xml_text = xml_path.read_text(encoding="utf-8", errors="ignore")
                row = parse_booking_info(xml_text)
                em = (row.get("email") or "").strip().lower()
                if not em:
                    continue

                if email_kind == "booking":
                    if em.endswith("@guest.booking.com"):
                        rows.append(row)
                        kept += 1
                else:
                    if not any(em.endswith(dom) for dom in EXCLUDE_EMAIL_DOMAINS):
                        rows.append(row)
                        kept += 1
            except Exception as e:
                logger.warning(f"[BUILD_EMAILS] Failed parse XML {xml_path}: {e}")

        if rows:
            total_emails += len(rows)
            out = write_hotel_emails_txt(hotel_name, rows, report_dir)
            out_paths.append(out)
        log_duration("BUILD_EMAILS per PMS", t1, f"(PMS={pms}, files={count_xml}, rows_kept={kept})")

    log_duration("BUILD_EMAILS total", t0, f"(TXT files={len(out_paths)}, emails={total_emails}, kind={email_kind})")
    return out_paths, total_emails


def create_zip(files: List[Path], archive_path: Path) -> Path:
    t0 = time.perf_counter()
    zpath = archive_path.with_suffix(".zip")
    with zipfile.ZipFile(zpath, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=5) as z:
        for f in files:
            z.write(f, arcname=f.name)
    log_duration("ZIP", t0, f"(files={len(files)}, out={zpath})")
    return zpath


# ---------------- Playwright/UI ----------------
async def do_login(page, username: str, password: str):
    t0 = time.perf_counter()
    logger.info("[LOGIN] Start goto/login")
    await page.goto(URL, wait_until="domcontentloaded", timeout=60000)
    await page.wait_for_load_state("networkidle", timeout=60000)
    log_duration("LOGIN: page load", t0)

    # email
    t1 = time.perf_counter()
    email_inp = None
    try:
        email_inp = page.get_by_placeholder("Enter your email id").first
        await email_inp.wait_for(state="visible", timeout=4000)
    except Exception:
        pass
    if not email_inp:
        for sel in [
            "css=input[placeholder='Enter your email id']",
            "css=input[placeholder*='email id' i]",
            "css=input[aria-label*='Email' i]",
            "css=input[type='email']",
        ]:
            loc = page.locator(sel).first
            try:
                await loc.wait_for(state="visible", timeout=3000)
                email_inp = loc
                break
            except Exception:
                continue
    if not email_inp:
        raise RuntimeError("Не нашёл поле Email")
    log_duration("LOGIN: email input ready", t1)

    t2 = time.perf_counter()
    pass_inp = None
    for sel in ["css=input[type='password']", "css=input[aria-label*='Password' i]"]:
        loc = page.locator(sel).first
        try:
            await loc.wait_for(state="visible", timeout=4000)
            pass_inp = loc
            break
        except Exception:
            continue
    if not pass_inp:
        raise RuntimeError("Не нашёл поле Password")
    log_duration("LOGIN: password input ready", t2)

    async def robust_fill_input(inp_loc, value):
        await inp_loc.click()
        await inp_loc.fill("")
        await inp_loc.type(value, delay=20)
        try:
            v = await inp_loc.input_value()
        except Exception:
            v = ""
        if v.strip() != value:
            await page.evaluate(
                "(el, val) => { el.value = val; el.dispatchEvent(new Event('input', {bubbles:true})); el.dispatchEvent(new Event('change', {bubbles:true})); }",
                await inp_loc.element_handle(), value
            )

    t3 = time.perf_counter()
    await robust_fill_input(email_inp, username)
    await robust_fill_input(pass_inp, password)
    log_duration("LOGIN: typed credentials", t3)

    t4 = time.perf_counter()
    clicked = False
    for sel in [
        "css=button[type=submit]",
        "css=button:has-text('Login')",
        "xpath=//button[normalize-space()='Login' or contains(.,'Login')]"
    ]:
        try:
            await page.locator(sel).first.click(timeout=2000)
            clicked = True
            break
        except Exception:
            continue
    if not clicked:
        await pass_inp.press("Enter")

    try:
        await page.wait_for_selector(
            "mat-sidenav-container, mat-drawer, button.mat-icon-button, #menu, [aria-label*=menu i]",
            timeout=20000
        )
    except Exception:
        pass

    await page.wait_for_load_state("networkidle", timeout=30000)
    log_duration("LOGIN: submit and post-wait", t4)
    log_duration("LOGIN total", t0)

async def open_menu_and_go(page, item_text: str):
    t0 = time.perf_counter()
    logger.info("[NAV] Open side menu and go to target page")

    for _ in range(2):
        try:
            await page.mouse.click(28, 96)
            await asyncio.sleep(0.1)
            break
        except Exception:
            pass

    for _ in range(3):
        opened = False
        for sel in ["i.fa-bars", "button:has(i.fa-bars)", "[aria-label*=menu i]", "button.mat-icon-button"]:
            try:
                await page.locator(sel).first.click(timeout=800)
                opened = True
                await asyncio.sleep(0.2)
                break
            except Exception:
                continue
        if opened:
            break

    for _ in range(3):
        try:
            el = page.locator("xpath=//*[self::a or self::button or self::div][normalize-space()='Bookings']").first
            if await el.is_visible():
                await el.scroll_into_view_if_needed()
                await el.click(timeout=2000)
                await asyncio.sleep(0.3)
                break
        except Exception:
            await asyncio.sleep(0.3)

    target_selectors = [
        f"text={item_text}",
        "xpath=//*[self::a or self::button or self::div][contains(normalize-space(.), 'Bookings from Channels to (FN & FX)')]",
        "xpath=//*[contains(normalize-space(.), 'Bookings from Channels to') and contains(.,'(FN & FX)')]",
    ]
    clicked = False
    for _ in range(5):
        for sel in target_selectors:
            try:
                el = page.locator(sel).first
                if await el.is_visible():
                    await el.scroll_into_view_if_needed()
                    await el.click(timeout=3000)
                    clicked = True
                    break
            except Exception:
                continue
        if clicked:
            break
        await page.mouse.wheel(0, 1000)
        await asyncio.sleep(0.3)

    if not clicked:
        raise RuntimeError("Не нашёл/не кликнул подпункт.")

    ok = False
    for _ in range(5):
        for sel in [
            "text=Bookings from Channels to (FN & FX)",
            "xpath=//*[self::h1 or self::h2 or self::h3][contains(.,'Bookings from Channels to (FN & FX)')]",
            "xpath=//ngc-multiselect-dropdown",
            "xpath=//*[contains(@class,'dropdown-btn')]//span[contains(.,'Select Property')]",
            "text=Select Property",
        ]:
            try:
                if await page.locator(sel).first.is_visible():
                    ok = True
                    break
            except Exception:
                continue
        if ok:
            break
        await asyncio.sleep(0.6)

    if not ok:
        content = (await page.content()).lower()
        if "fn & fx" in content or "select property" in content:
            ok = True

    if not ok:
        raise RuntimeError("Переход не подтвердился (нет заголовка).")

    log_duration("NAV: open menu and go", t0)

async def open_property_dropdown(page):
    t0 = time.perf_counter()
    opener = None
    for sel in [
        "xpath=//ngc-multiselect-dropdown//div[contains(@class,'dropdown-btn')][.//span[contains(normalize-space(),'Select Property')]]",
        "xpath=//*[contains(@class,'multiselect-dropdown')]//div[contains(@class,'dropdown-btn')][.//span[contains(normalize-space(),'Select Property')]]",
        "text=Select Property"
    ]:
        loc = page.locator(sel).first
        try:
            await loc.wait_for(state="visible", timeout=4000)
            opener = loc
            break
        except Exception:
            continue
    if not opener:
        for sel in ["css=ngc-multiselect-dropdown .dropdown-btn", "css=.multiselect-dropdown .dropdown-btn"]:
            loc = page.locator(sel).first
            try:
                await loc.wait_for(state="visible", timeout=1500)
                opener = loc
                break
            except Exception:
                continue
    if not opener:
        raise RuntimeError("Не нашёл 'Select Property'.")
    await opener.click()
    panel = page.locator("css=.dropdown-list:not([hidden])").last
    await panel.wait_for(state="visible", timeout=3000)
    log_duration("UI: open property dropdown", t0)
    return panel

async def list_hotels_from_dropdown(page) -> List[str]:
    t0 = time.perf_counter()
    panel = await open_property_dropdown(page)
    texts = await panel.evaluate(
        """(root) => Array.from(root.querySelectorAll('li'))
                      .map(li => (li.textContent||'').trim())
                      .filter(Boolean)"""
    )
    try:
        await page.keyboard.press("Escape")
    except Exception:
        pass
    log_duration("UI: list_hotels_from_dropdown", t0, f"(hotels={len(texts)})")
    return texts


# ---------------- API via AIOHTTP ----------------
def _ms_to_seconds(ms: int) -> float:
    return max(0.1, ms/1000.0)

async def post_json_with_retry_aiohttp(
    session: aiohttp.ClientSession,
    url: str,
    payload: dict, *,
    attempts: int,
    timeout_ms: int,
    base_delay: float,
    jitter: float,
) -> Optional[Any]:
    delay = base_delay
    last_err = None
    t0 = time.perf_counter()
    timeout = aiohttp.ClientTimeout(total=_ms_to_seconds(timeout_ms))

    for i in range(1, attempts + 1):
        t_try = time.perf_counter()
        try:
            async with session.post(
                url,
                json=payload,
                headers={
                    "content-type": "application/json",
                    "origin": URL,
                    "referer": URL + "/",
                    "accept": "application/json, text/plain, */*",
                },
                timeout=timeout
            ) as resp:
                status = resp.status
                txt = await resp.text()
                if 200 <= status < 400:
                    try:
                        js = await resp.json()
                    except Exception:
                        try:
                            js = json.loads(txt)
                        except Exception:
                            js = txt
                    logger.info(f"[HTTP] OK {status} {url} in {(time.perf_counter()-t_try):.3f}s")
                    log_duration("HTTP total", t0, f"({url})")
                    return js
                last_err = f"HTTP {status}: {txt[:300]}"
                logger.warning(f"[HTTP] Fail attempt {i}/{attempts} {url} in {(time.perf_counter()-t_try):.3f}s: {last_err}")
        except asyncio.TimeoutError as te:
            last_err = f"Timeout: {te}"
            logger.warning(f"[HTTP] Timeout attempt {i}/{attempts} {url} in {(time.perf_counter()-t_try):.3f}s")
        except Exception as e:
            last_err = f"Exception: {e}"
            logger.warning(f"[HTTP] Exception attempt {i}/{attempts} {url}: {e}")

        if i < attempts:
            sleep_s = delay + random.uniform(0.0, jitter)
            logger.info(f"[HTTP] Retry in {sleep_s:.2f}s -> {url}")
            await asyncio.sleep(sleep_s)
            delay *= 2

    logger.error(f"[HTTP] POST {url} failed after {attempts} attempts: {last_err}")
    log_duration("HTTP total", t0, f"(FAILED {url})")
    return None

async def api_is_bookinglog_aio(
    session: aiohttp.ClientSession,
    pmscode: int, from_date: str, to_date: str, cmcode: str
) -> List[Dict[str, Any]]:
    t0 = time.perf_counter()
    url = f"{API_BASE}/api/Bookinglog/IsBookinglog"
    payload = {
        "PmsCode": pmscode,
        "CMCode": cmcode,
        "From": from_date,
        "To": to_date,
        "PaginationFromId": "0",
        "PaginationToId": "50",
        "Search": ""
    }
    js = await post_json_with_retry_aiohttp(
        session, url, payload,
        attempts=BOOKLOG_RETRY_ATTEMPTS,
        timeout_ms=BOOKLOG_TIMEOUT_MS,
        base_delay=BOOKLOG_BASE_DELAY,
        jitter=BOOKLOG_JITTER,
    )
    if isinstance(js, list):
        log_duration("API BookingLog", t0, f"(pms={pmscode}, rows={len(js)})")
        return js
    log_duration("API BookingLog", t0, f"(pms={pmscode}, rows=0; bad-response)")
    return []

async def api_get_xml_aio(
    session: aiohttp.ClientSession,
    pmscode: int, token: int, cmcode: str, xml_type: str = "ReceivedXML"
) -> str:
    t0 = time.perf_counter()
    url = f"{API_BASE}/api/AriXml/IsAriBookXml"
    payload = {"pmscode": pmscode, "cmcode": cmcode, "token": token, "Type": xml_type}
    js = await post_json_with_retry_aiohttp(
        session, url, payload,
        attempts=RETRY_ATTEMPTS,
        timeout_ms=REQ_TIMEOUT_MS,
        base_delay=RETRY_BASE_DELAY,
        jitter=RETRY_JITTER
    )
    xml = ""
    if isinstance(js, dict):
        xml = js.get("xmlData") or ""
    elif isinstance(js, list) and js:
        first = js[0]
        if isinstance(first, dict):
            xml = first.get("xmlData") or ""
    elif isinstance(js, str):
        xml = js
    log_duration("API GetXML", t0, f"(pms={pmscode}, token={token}, got={bool(xml)})")
    return xml


# ---------------- Очередь записи ----------------
async def writer_worker(queue: asyncio.Queue):
    logger.info("[WRITER] Writer worker started")
    written = 0
    while True:
        item = await queue.get()
        if item is None:
            queue.task_done()
            logger.info(f"[WRITER] Writer worker stop. Written={written}")
            break
        pms_dir, token, xml_text = item
        try:
            pms_dir.mkdir(parents=True, exist_ok=True)
            path = pms_dir / f"{token}.xml"
            path.write_text(xml_text, encoding="utf-8")
            written += 1
            if written % 1000 == 0:
                logger.info(f"[WRITER] Written so far: {written}")
        except Exception as e:
            logger.warning(f"[WRITER] Failed write token={token} -> {e}")
        finally:
            queue.task_done()


async def fetch_single_token(
    session: aiohttp.ClientSession, pms: int, token: int,
    sem_token: asyncio.Semaphore, write_queue: asyncio.Queue, run_dir: Path
) -> bool:
    async with sem_token:
        try:
            xml = await api_get_xml_aio(session, pms, token, DEFAULT_CM_CODE, "ReceivedXML")
            if not xml:
                return False
            pms_dir = run_dir / "xml" / str(pms)
            await write_queue.put((pms_dir, token, xml))
            return True
        except Exception as e:
            logger.warning(f"[FETCH_XML] token={token} pms={pms} -> {e}")
            return False


async def process_single_pms(
    session: aiohttp.ClientSession, pms: int,
    sem_pms: asyncio.Semaphore, sem_token: asyncio.Semaphore,
    write_queue: asyncio.Queue, date_from: str, date_to: str,
    cm_code: str, run_dir: Path
) -> int:
    t0 = time.perf_counter()
    async with sem_pms:
        try:
            booking_log = await api_is_bookinglog_aio(session, pms, date_from, date_to, cm_code)
            if not booking_log:
                logger.info(f"[BOOKLOG] pms={pms} -> no rows")
                log_duration("FETCH PMS total", t0, f"(pms={pms}, saved=0, tokens=0)")
                return 0

            tokens: List[int] = []
            for row in booking_log:
                token_raw = row.get("echoToken")
                try:
                    token = int(float(token_raw))
                except Exception:
                    token = 0
                if token:
                    tokens.append(token)

            if not tokens:
                logger.info(f"[BOOKLOG] pms={pms} -> no tokens")
                log_duration("FETCH PMS total", t0, f"(pms={pms}, saved=0, tokens=0)")
                return 0

            tasks = [
                fetch_single_token(session, pms, token, sem_token, write_queue, run_dir)
                for token in tokens
            ]
            results = await asyncio.gather(*tasks, return_exceptions=True)
            saved = sum(1 for r in results if isinstance(r, bool) and r)
            logger.info(f"[BOOKLOG] pms={pms} -> rows={len(booking_log)}; tokens={len(tokens)}; saved={saved}")
            log_duration("FETCH PMS total", t0, f"(pms={pms}, saved={saved}, tokens={len(tokens)})")
            return saved
        except Exception as e:
            logger.exception(f"[PMS] process_single_pms error pms={pms}: {e}")
            return 0


# ---------------- TELEGRAM BOT ----------------
bot = Bot(token=TOKEN)
dp  = Dispatcher()

@dp.message(CommandStart())
async def cmd_start(m: Message, state: FSMContext):
    await state.clear()
    await m.answer("Привет! Введи логин (email) для входа в DataHub:")
    await state.set_state(AuthFlow.waiting_username)

@dp.message(AuthFlow.waiting_username)
async def get_username(m: Message, state: FSMContext):
    await state.update_data(username=m.text.strip())
    await m.answer("Теперь введи пароль:")
    await state.set_state(AuthFlow.waiting_password)

@dp.message(AuthFlow.waiting_password)
async def get_password(m: Message, state: FSMContext):
    await state.update_data(password=m.text.strip())
    await m.answer("Пробую авторизоваться...")

    data = await state.get_data()
    username = data["username"]
    password = data["password"]

    try:
        t0 = time.perf_counter()
        async with async_playwright() as p:
            browser = await p.chromium.launch(
                headless=True,
                args=["--no-sandbox","--disable-dev-shm-usage","--disable-extensions","--disable-gpu"]
            )
            context = await browser.new_context()
            page = await context.new_page()
            await do_login(page, username, password)
            await open_menu_and_go(page, MENU_ITEM)
            await browser.close()
        log_duration("AUTH total", t0)
        await m.answer("✅ Авторизация прошла успешно! Введи даты в формате: `YYYY-MM-DD YYYY-MM-DD` (например: `2025-09-12 2025-09-13`).", parse_mode="Markdown")
        await state.set_state(AuthFlow.waiting_dates)
    except Exception as e:
        await send_error(m, "Авторизация", e)
        await m.answer("Попробуй ещё раз /start")
        await state.clear()

@dp.message(AuthFlow.waiting_dates)
async def get_dates_and_start(m: Message, state: FSMContext):
    txt = (m.text or "").strip()
    parts = txt.split()
    if len(parts) != 2:
        await m.answer("Нужно ввести две даты через пробел: `YYYY-MM-DD YYYY-MM-DD`.\nНапример: `2025-09-12 2025-09-13`", parse_mode="Markdown")
        return
    date_from, date_to = parts
    await state.update_data(date_from=date_from, date_to=date_to)

    await m.answer("Выбери, что спарсить:", reply_markup=KB_PARSE_CHOICE)
    await state.set_state(AuthFlow.waiting_choice)

@dp.message(AuthFlow.waiting_choice)
async def select_numbers_or_emails(m: Message, state: FSMContext):
    text = (m.text or "").strip().lower()
    if "номера" in text:
        await state.update_data(parse_mode="numbers")
        await m.answer("Выбери формат выгрузки номеров:", reply_markup=KB_NUMBERS_FMT)
        await state.set_state(AuthFlow.waiting_numbers_fmt)   # <-- идём выбирать формат
    elif "почт" in text:
        await state.update_data(parse_mode="emails")
        await m.answer("Выбери тип почт:", reply_markup=KB_EMAIL_KIND)
        await state.set_state(AuthFlow.waiting_email_kind)
    else:
        await m.answer("Нажми одну из кнопок ниже.", reply_markup=KB_PARSE_CHOICE)

@dp.message(AuthFlow.waiting_numbers_fmt)
async def select_numbers_fmt(m: Message, state: FSMContext):
    t = (m.text or "").strip().lower()
    if t == "word":
        await state.update_data(numbers_format="word")
    elif t == "kadir":
        await state.update_data(numbers_format="kadir")
    else:
        await m.answer("Выбери формат: Word или Kadir", reply_markup=KB_NUMBERS_FMT)
        return

    await m.answer("Ок, запускаю парсинг.", reply_markup=ReplyKeyboardRemove())
    data = await state.get_data()
    await start_job_from_state(m, data, parse_mode="numbers")
    await state.clear()

@dp.message(AuthFlow.waiting_email_kind)
async def select_email_kind(m: Message, state: FSMContext):
    text = (m.text or "").strip().lower()
    if "booking" in text:
        await state.update_data(email_kind="booking")
    elif "остальны" in text:
        await state.update_data(email_kind="other")
    else:
        await m.answer("Нажми одну из кнопок ниже.", reply_markup=KB_EMAIL_KIND)
        return

    await m.answer("Ок, запускаю парсинг.", reply_markup=ReplyKeyboardRemove())
    data = await state.get_data()
    await start_job_from_state(m, data, parse_mode="emails")
    await state.clear()

async def start_job_from_state(m: Message, data: dict, parse_mode: str):
    username  = data["username"]
    password  = data["password"]
    date_from = data["date_from"]
    date_to   = data["date_to"]
    email_kind = data.get("email_kind")

    safe_rmtree(OLD_XML_DIR)
    run_dir = WORK_ROOT / f"run_{m.chat.id}_{m.message_id}"
    safe_rmtree(run_dir)
    run_dir.mkdir(exist_ok=True, parents=True)
    logger.info(f"[RUN] Start job run_dir={run_dir} mode={parse_mode} email_kind={email_kind}")

    numbers_format = data.get("numbers_format", "word")
    asyncio.create_task(
        run_job_and_reply(
            m, username, password, date_from, date_to,
            DEFAULT_CM_CODE, run_dir,
            parse_mode=parse_mode, email_kind=email_kind, numbers_format=numbers_format
        )
    )
    await m.answer("Запустил парсинг. Это займёт некоторое время. Буду присылать прогресс.")


async def run_job_and_reply(m: Message, username: str, password: str, date_from: str, date_to: str,
                            cm_code: str, run_dir: Path, parse_mode: str = "numbers",
                            email_kind: Optional[str] = None, numbers_format: str = "word"):
    t_all = time.perf_counter()
    try:
        # 1) Получаем PMS->Name
        try:
            t0 = time.perf_counter()
            async with async_playwright() as p:
                browser = await p.chromium.launch(headless=True)
                context = await browser.new_context()
                page = await context.new_page()

                await do_login(page, username, password)
                await open_menu_and_go(page, MENU_ITEM)

                async def route_handler(route, request):
                    rtype = request.resource_type
                    url = request.url
                    if rtype in ("image", "font", "stylesheet"):
                        await route.abort(); return
                    if any(x in url for x in ["analytics", "googletag", "hotjar", "fonts.googleapis"]):
                        await route.abort(); return
                    await route.continue_()
                await context.route("**/*", route_handler)

                labels = await list_hotels_from_dropdown(page)
                await browser.close()
            log_duration("STEP 1: Collect PMS list", t0, f"(labels={len(labels)})")
        except Exception as e:
            await send_error(m, "Сбор списка PMS/отелей", e)
            return

        all_pms: List[int] = []
        pms_to_name: Dict[int, str] = {}
        for txt in labels:
            p = extract_pms_from_label(txt)
            if p:
                all_pms.append(p)
                name = txt.split("-", 1)[-1].strip()
                pms_to_name[p] = name
        all_pms = sorted(set(all_pms))
        logger.info(f"[PMS] Extracted PMS count={len(all_pms)}")
        await m.answer(f"Найдено {len(all_pms)} отелей (PMS). Начинаю загрузку XML...")
        if TEST_ONLY_PMS is not None:
            if TEST_ONLY_PMS in pms_to_name:
                all_pms = [TEST_ONLY_PMS]
                pms_to_name = {TEST_ONLY_PMS: pms_to_name[TEST_ONLY_PMS]}
                await m.answer(f"Тестовый режим: работаем только с PMS={TEST_ONLY_PMS} ({pms_to_name[TEST_ONLY_PMS]})")
            else:
                await m.answer(f"Тестовый режим: PMS={TEST_ONLY_PMS} не найден среди доступных ({len(pms_to_name)} шт.). Останавливаю.")
                return

        # 2) Получаем XML и пишем (aiohttp + большая параллельность)
        try:
            t0 = time.perf_counter()
            # Настраиваем сессию aiohttp с большим пулом соединений
            connector = aiohttp.TCPConnector(limit=400, limit_per_host=120, ttl_dns_cache=300)
            timeout = aiohttp.ClientTimeout(total=120)  # общий timeout на вызов
            async with aiohttp.ClientSession(connector=connector, timeout=timeout) as session:
                sem_pms   = asyncio.Semaphore(PMS_CONCURRENCY)
                sem_token = asyncio.Semaphore(TOKEN_CONCURRENCY)
                write_queue = asyncio.Queue(maxsize=WRITE_QUEUE_MAXSIZE)
                writer_tasks = [asyncio.create_task(writer_worker(write_queue)) for _ in range(WRITERS)]
                logger.info(f"[STEP2] Start fetching XML. PMS total={len(all_pms)}")

                # Параллельно по PMS
                pms_tasks = [
                    process_single_pms(session, pms, sem_pms, sem_token, write_queue, date_from, date_to, cm_code, run_dir)
                    for pms in all_pms
                ]

                NOTIFY_EVERY = 150  # присылать прогресс раз в 150 PMS
                total_saved = 0
                processed = 0
                total_pms = len(pms_tasks)
                # Ждём в порядке завершения для своевременного прогресса
                for coro in asyncio.as_completed(pms_tasks):
                    saved = await coro
                    total_saved += (saved or 0)
                    processed += 1

                    if (processed % NOTIFY_EVERY == 0) or (processed == total_pms):
                        try:
                            await m.answer(
                                f"Прогресс: обработано PMS {processed}/{total_pms}, "
                                f"XML сохранено: {total_saved}"
                            )
                        except Exception:
                            # если вдруг Telegram вернул flood, просто пропускаем это сообщение
                            pass

                # Завершаем писателей
                for _ in range(WRITERS):
                    await write_queue.put(None)
                await write_queue.join()
                await asyncio.gather(*writer_tasks, return_exceptions=True)
            log_duration("STEP 2: Fetch XML total", t0, f"(XML saved={total_saved})")
        except Exception as e:
            await send_error(m, "Загрузка XML", e)
            return

        await m.answer("Загрузка XML завершена. Формирую TXT-отчёты...")

        # 3) TXT-отчёты + подсчёты
        try:
            t0 = time.perf_counter()
            if parse_mode == "numbers": 
                fmt = (numbers_format or "word").lower()
                if fmt == "kadir":
                    # CSV с тегами (формат Kadir)
                    reports, total_rows = build_kadir_merged(pms_to_name, run_dir)
                    if not reports:
                        await m.answer("Готово. Не удалось сформировать отчёты (нет данных).")
                        safe_rmtree(run_dir)
                        return
                    await m.answer(
                        f"Сформирован общий CSV: {len(reports)} файл.\n"
                        f"Всего записей: {total_rows}\nУпаковываю в ZIP..."
                    )   
                    final_caption = f"Готово! CSV: 1 | Записей: {total_rows} (формат Kadir)"
                else:
                    # Word: как раньше (TXT по телефонам)
                    reports, total_rows, _ = build_hotel_reports(pms_to_name, run_dir)
                    if not reports:
                        await m.answer("Готово. Не удалось сформировать отчёты (нет данных).")
                        safe_rmtree(run_dir)
                        return
                    await m.answer(
                        f"Сформировано отчётов: {len(reports)}.\n"
                        f"Всего номеров: {total_rows}\nУпаковываю в ZIP..."
                    )
                    final_caption = f"Готово! TXT: {len(reports)} | Номеров: {total_rows}"
            else:
                reports, total_emails = build_email_reports(pms_to_name, run_dir, email_kind=email_kind or "other")
                if not reports:
                    await m.answer("Готово. Не удалось сформировать отчёты (нет данных).")
                    safe_rmtree(run_dir)
                    return
                label = "Booking-почты" if (email_kind or "") == "booking" else "Все остальные почты"
                await m.answer(f"Сформировано отчётов: {len(reports)}.\nВсего e-mail: {total_emails} ({label})\nУпаковываю в ZIP...")
                final_caption = f"Готово! TXT: {len(reports)} | Email: {total_emails} ({label})"
            log_duration("STEP 3: Build reports", t0, f"(reports={len(reports)})")
        except Exception as e:
            await send_error(m, "Формирование TXT", e)
            return

        # 4) Архив (ZIP) и отправка
        try:
            t0 = time.perf_counter()
            archive_path = run_dir / "reports"
            final_archive = create_zip(reports, archive_path)
            await m.answer_document(FSInputFile(final_archive), caption=final_caption)
            log_duration("STEP 4: Zip+send", t0)
        except Exception as e:
            await send_error(m, "Архивирование/отправка", e)
            return
    except Exception as e:
        await send_error(m, "Общая ошибка", e)
    finally:
        log_duration("JOB total", t_all)
        try:
            safe_rmtree(run_dir)
            safe_rmtree(OLD_XML_DIR)
        except Exception as e:
            logger.warning(f"[CLEANUP] Failed post-cleanup: {e}")


# ---------------- MAIN ----------------
def main():
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s | %(levelname)-7s | %(name)s | %(message)s",
        datefmt="%Y-%m-%d %H:%M:%S"
    )
    if not TOKEN:
        raise RuntimeError("Не задан BOT_TOKEN (переменная окружения). Создайте .env и задайте BOT_TOKEN=...")

    pd.options.mode.copy_on_write = True
    logger.info("[BOOT] Starting bot polling...")
    dp.run_polling(bot, allowed_updates=["message"])

if __name__ == "__main__":
    main()
