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
from pathlib import Path
from typing import List, Dict, Any, Optional, Tuple

import pandas as pd
from aiogram import Bot, Dispatcher, F
from aiogram.types import Message, FSInputFile
from aiogram.filters import CommandStart
from aiogram.fsm.state import StatesGroup, State
from aiogram.fsm.context import FSMContext
from dotenv import load_dotenv

from playwright.async_api import async_playwright, TimeoutError as PWTimeout

# ---------------- CONFIG ----------------
load_dotenv()
TOKEN = os.getenv("BOT_TOKEN")  # из .env

API_BASE  = "https://idsdatahubdashboardapi.azurewebsites.net"
URL       = "https://datahubdashboard.idsnext.live"
MENU_ITEM = "Bookings from Channels to (FN & FX)"

# Скорости/ограничения
CONCURRENCY       = 32            # загрузка XML
REQ_TIMEOUT_MS    = 60_000
RETRY_ATTEMPTS    = 3
RETRY_BASE_DELAY  = 0.5
RETRY_JITTER      = 0.3

BOOKLOG_CONCURRENCY    = 5        # параллелизм для IsBookinglog
BOOKLOG_TIMEOUT_MS     = 25_000   # меньше, чтобы "мертвые" каналы не стопорили
BOOKLOG_RETRY_ATTEMPTS = 3
BOOKLOG_JITTER         = 0.4
BOOKLOG_BASE_DELAY     = 0.6

WRITERS = 8
WRITE_QUEUE_MAXSIZE = 5000

WORK_ROOT = Path("work_runs")
WORK_ROOT.mkdir(exist_ok=True)
OLD_XML_DIR = Path("xml_api")  # из старых запусков — будем чистить

SAFE_CHARS = re.compile(r'[\\/*?:"<>|]+')

# --- набор каналов, по которым ходим (можете расширять)
CM_CANDIDATES = [
    "CM1000",   # STAAH
    "CM7000",   # RESAVENUE
    "CM4000",   # MAXIMOJO
    "CM1123",   # HOBSE
    "CM9902",   # SABRE
    "CM3000",   # TRAVELGURU (пример; если нет — просто вернёт пусто)
]

# Тестовый режим: один PMS
TEST_ONLY_PMS = None   # например 7, чтобы тестировать только один отель


# ---------------- FSM ----------------
class AuthFlow(StatesGroup):
    waiting_username = State()
    waiting_password = State()
    waiting_dates    = State()


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
    if len(msg) > 3500:
        msg = msg[:3490] + "…`"
    await m.answer(msg, parse_mode="Markdown")

def safe_rmtree(path: Path):
    try:
        if path.exists():
            shutil.rmtree(path, ignore_errors=True)
    except Exception:
        pass


# ========= ПАРСИНГ XML =========
def parse_booking_info(xml_text: str) -> dict:
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
    return path


def build_hotel_reports(pms_to_name: dict[int, str], run_dir: Path) -> Tuple[List[Path], int, int]:
    out_paths = []
    save_dir = run_dir / "xml"
    report_dir = run_dir / "reports"
    report_dir.mkdir(exist_ok=True, parents=True)

    total_rows = 0
    total_emails = 0

    for pms, hotel_name in pms_to_name.items():
        pms_dir = save_dir / str(pms)
        if not pms_dir.exists():
            continue
        rows = []
        for xml_path in sorted(pms_dir.glob("*.xml")):
            try:
                xml_text = xml_path.read_text(encoding="utf-8", errors="ignore")

                if not is_booking_com_xml(xml_text):
                    continue

                row = parse_booking_info(xml_text)
                if any((row.get("start"), row.get("end"), row.get("given"), row.get("surname"),
                        row.get("phone"), row.get("email"), row.get("total"))):
                    rows.append(row)
            except Exception:
                pass

        if rows:
            total_rows += len(rows)
            total_emails += sum(1 for r in rows if (r.get("email") or "").strip())
            out = write_hotel_txt(hotel_name, rows, report_dir)
            out_paths.append(out)

    return out_paths, total_rows, total_emails


def create_zip(files: List[Path], archive_path: Path) -> Path:
    zpath = archive_path.with_suffix(".zip")
    with zipfile.ZipFile(zpath, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=5) as z:
        for f in files:
            z.write(f, arcname=f.name)
    return zpath


# ---------------- Playwright/UI ----------------
async def do_login(page, username: str, password: str):
    await page.goto(URL, wait_until="domcontentloaded", timeout=60000)
    await page.wait_for_load_state("networkidle", timeout=60000)

    # email
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

    pass_inp = None
    for sel in ["css=input[type='password']", "css=input[aria-label*='Password' i]"]:
        loc = page.locator(sel).first
        try:
            await loc.wait_for(state="visible", timeout=4000)
            pass_inp = loc
            break
        except Exception:
            continue
    if not pass_inп:
        raise RuntimeError("Не нашёл поле Password")

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

    await robust_fill_input(email_inп, username)
    await robust_fill_input(pass_inп, password)

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
        await pass_inп.press("Enter")

    try:
        await page.wait_for_selector(
            "mat-sidenav-container, mat-drawer, button.mat-icon-button, #menu, [aria-label*=menu i]",
            timeout=20000
        )
    except Exception:
        pass

    await page.wait_for_load_state("networkidle", timeout=30000)

async def open_menu_and_go(page, item_text: str):
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

async def open_property_dropdown(page):
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
    return panel

async def list_hotels_from_dropdown(page) -> List[str]:
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
    return texts


# ---------------- API ----------------
async def post_json_with_retry(
    req, url: str, payload: dict, *,
    attempts: int = RETRY_ATTEMPTS,
    timeout_ms: int = REQ_TIMEOUT_MS,
    base_delay: float = RETRY_BASE_DELAY,
    jitter: float = RETRY_JITTER,
):
    delay = base_delay
    last_err = None

    for i in range(1, attempts + 1):
        try:
            resp = await req.post(
                url,
                data=json.dumps(payload),
                headers={
                    "content-type": "application/json",
                    "origin": URL,
                    "referer": URL + "/",
                    "accept": "application/json, text/plain, */*",
                },
                timeout=timeout_ms,
            )
            status = resp.status
            txt = await resp.text()
            if 200 <= status < 400:
                try:
                    return await resp.json()
                except Exception:
                    try:
                        return json.loads(txt)
                    except Exception:
                        return txt
            last_err = f"HTTP {status}: {txt[:300]}"
        except PWTimeout as te:
            last_err = f"Timeout: {te}"
        except Exception as e:
            last_err = f"Exception: {e}"

        if i < attempts:
            await asyncio.sleep(delay + random.uniform(0.0, jitter))
            delay *= 2

    print(f"[ERROR] POST {url} failed after {attempts} attempts: {last_err}")
    return None

async def api_is_bookinglog_ctx(req, pmscode: int, from_date: str, to_date: str, cmcode: str) -> List[Dict[str, Any]]:
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
    await asyncio.sleep(random.uniform(0.05, 0.25))
    js = await post_json_with_retry(
        req, url, payload,
        attempts=BOOKLOG_RETRY_ATTEMPTS,
        timeout_ms=BOOKLOG_TIMEOUT_MS,
        base_delay=BOOKLOG_BASE_DELAY,
        jitter=BOOKLOG_JITTER,
    )
    if isinstance(js, list):
        return js
    return []

async def api_get_xml_ctx(req, pmscode: int, token: int, cmcode: str, xml_type: str = "ReceivedXML") -> str:
    url = f"{API_BASE}/api/AriXml/IsAriBookXml"
    payload = {"pmscode": pmscode, "cmcode": cmcode, "token": token, "Type": xml_type}
    js = await post_json_with_retry(req, url, payload)
    if isinstance(js, dict):
        xml = js.get("xmlData") or ""
        return xml if isinstance(xml, str) else ""
    if isinstance(js, list) and js:
        first = js[0]
        if isinstance(first, dict):
            xml = first.get("xmlData") or ""
            return xml if isinstance(xml, str) else ""
    if isinstance(js, str):
        return js
    return ""


# ---------------- Очередь записи ----------------
async def writer_worker(queue: asyncio.Queue):
    while True:
        item = await queue.get()
        if item is None:
            queue.task_done()
            break
        pms_dir, token, xml_text = item
        try:
            pms_dir.mkdir(parents=True, exist_ok=True)
            path = pms_dir / f"{token}.xml"
            path.write_text(xml_text, encoding="utf-8")
        finally:
            queue.task_done()

async def _fetch_single_xml_ctx(req, pms: int, token: int, sem_xml: asyncio.Semaphore, write_queue: asyncio.Queue, run_dir: Path) -> bool:
    async with sem_xml:
        try:
            # cmcode не нужен для получения самого XML — он вкладывается в токен
            xml = await api_get_xml_ctx(req, pms, token, "CM1000")  # поле cmcode игнорируется беком; оставим любой
            if not xml:
                return False
            pms_dir = run_dir / "xml" / str(pms)
            await write_queue.put((pms_dir, token, xml))
            return True
        except Exception:
            return False

# --- получаем ВСЕ токены для одного PMS по нескольким каналам
async def fetch_tokens_for_pms_all_cm(
    req, pms: int, sem_booklog: asyncio.Semaphore,
    date_from: str, date_to: str, cm_codes: list[str]
) -> set[int]:
    tokens: set[int] = set()

    async def _load_one(cm: str) -> None:
        try:
            async with sem_booklog:
                booking_log = await api_is_bookinglog_ctx(req, pms, date_from, date_to, cm)
            for row in booking_log or []:
                tr = row.get("echoToken")
                try:
                    t = int(float(tr))
                    if t:
                        tokens.add(t)
                except Exception:
                    continue
        except Exception:
            # канал не дал ответ — просто пропускаем
            pass

    tasks = [asyncio.create_task(_load_one(cm)) for cm in cm_codes]
    # ждём завершения всех каналов, но не блокируемся на одном
    await asyncio.gather(*tasks, return_exceptions=True)
    return tokens

# --- одна PMS целиком: собираем токены по всем каналам, затем тянем XML
async def fetch_xml_for_pms_multi_cm(
    req,
    pms: int,
    sem_xml: asyncio.Semaphore,
    write_queue: asyncio.Queue,
    sem_booklog: asyncio.Semaphore,
    date_from: str,
    date_to: str,
    cm_codes: list[str],
    run_dir: Path
) -> int:
    try:
        all_tokens = await fetch_tokens_for_pms_all_cm(
            req, pms, sem_booklog, date_from, date_to, cm_codes
        )
        if not all_tokens:
            return 0

        tasks = [ _fetch_single_xml_ctx(req, pms, t, sem_xml, write_queue, run_dir)
                  for t in all_tokens ]
        results = await asyncio.gather(*tasks, return_exceptions=True)
        return sum(1 for r in results if isinstance(r, bool) and r)
    except Exception:
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

    data = await state.get_data()
    username = data["username"]
    password = data["password"]

    safe_rmtree(OLD_XML_DIR)
    run_dir = WORK_ROOT / f"run_{m.chat.id}_{m.message_id}"
    safe_rmtree(run_dir)
    run_dir.mkdir(exist_ok=True, parents=True)

    asyncio.create_task(run_job_and_reply(m, username, password, date_from, date_to, run_dir))
    await m.answer("Запустил парсинг. Это займёт некоторое время. Буду присылать прогресс.")
    await state.clear()

async def run_job_and_reply(m: Message, username: str, password: str, date_from: str, date_to: str, run_dir: Path):
    try:
        # 1) Получаем PMS->Name
        try:
            async with async_playwright() as p:
                browser = await p.chromium.launch(headless=True)
                context = await browser.new_context()
                page = await context.new_page()

                await do_login(page, username, password)
                await open_menu_and_go(page, MENU_ITEM)

                # Немного чистим ресурсы
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
        await m.answer(f"Найдено {len(all_pms)} отелей (PMS). Начинаю загрузку XML...")

        # Тестовый PMS
        if TEST_ONLY_PMS is not None:
            if TEST_ONLY_PMS in pms_to_name:
                all_pms = [TEST_ONLY_PMS]
                pms_to_name = {TEST_ONLY_PMS: pms_to_name[TEST_ONLY_PMS]}
                await m.answer(f"Тестовый режим: работаем только с PMS={TEST_ONLY_PMS} ({pms_to_name[TEST_ONLY_PMS]})")
            else:
                await m.answer(f"Тестовый режим: PMS={TEST_ONLY_PMS} не найден среди доступных ({len(pms_to_name)} шт.). Останавливаю.")
                return

        # 2) Получаем XML и пишем (по всем каналам из CM_CANDIDATES)
        try:
            async with async_playwright() as p:
                browser = await p.chromium.launch(headless=True)
                context = await browser.new_context()
                req = context.request

                sem_xml = asyncio.Semaphore(CONCURRENCY)
                sem_booklog = asyncio.Semaphore(BOOKLOG_CONCURRENCY)
                write_queue = asyncio.Queue(maxsize=WRITE_QUEUE_MAXSIZE)
                writer_tasks = [asyncio.create_task(writer_worker(write_queue)) for _ in range(WRITERS)]

                total_saved = 0
                finished = 0
                REPORT_EVERY = 10  # каждые 10 PMS обновляем прогресс

                tasks = [
                    asyncio.create_task(
                        fetch_xml_for_pms_multi_cm(
                            req, pms, sem_xml, write_queue, sem_booklog,
                            date_from, date_to, CM_CANDIDATES, run_dir
                        )
                    )
                    for pms in all_pms
                ]

                for fut in asyncio.as_completed(tasks):
                    try:
                        saved = await fut
                        if isinstance(saved, int):
                            total_saved += saved
                    except Exception:
                        pass
                    finally:
                        finished += 1
                        if finished % REPORT_EVERY == 0 or finished == len(tasks):
                            await m.answer(f"Прогресс: обработано PMS {finished}/{len(tasks)}, XML сохранено: {total_saved}")

                # Завершаем писателей
                for _ in range(WRITERS):
                    await write_queue.put(None)
                await write_queue.join()
                await asyncio.gather(*writer_tasks, return_exceptions=True)
                await browser.close()
        except Exception as e:
            await send_error(m, "Загрузка XML", e)
            return

        await m.answer("Загрузка XML завершена. Формирую TXT-отчёты...")

        # 3) TXT-отчёты + подсчёты
        try:
            reports, total_rows, total_emails = build_hotel_reports(pms_to_name, run_dir)
            if not reports:
                await m.answer("Готово. Не удалось сформировать отчёты (нет данных).")
                safe_rmtree(run_dir)
                return
        except Exception as e:
            await send_error(m, "Формирование TXT", e)
            return

        await m.answer(f"Сформировано отчётов: {len(reports)}.\n"
                       f"Всего номеров: {total_rows}\n"
                       f"Всего email'ов: {total_emails}\n"
                       f"Упаковываю в ZIP...")

        # 4) Архив (ZIP) и отправка
        try:
            archive_path = run_dir / "reports"
            final_archive = create_zip(reports, archive_path)
            await m.answer_document(FSInputFile(final_archive),
                                    caption=f"Готово! TXT: {len(reports)} | Номеров: {total_rows} | Email: {total_emails}")
        except Exception as e:
            await send_error(m, "Архивирование/отправка", e)
            return
    except Exception as e:
        await send_error(m, "Общая ошибка", e)
    finally:
        try:
            safe_rmtree(run_dir)
            safe_rmtree(OLD_XML_DIR)
        except Exception:
            pass


# ---------------- MAIN ----------------
def main():
    import logging
    logging.basicConfig(level=logging.INFO)
    if not TOKEN:
        raise RuntimeError("Не задан BOT_TOKEN (переменная окружения). Создайте .env и задайте BOT_TOKEN=...")

    pd.options.mode.copy_on_write = True
    dp.run_polling(bot, allowed_updates=["message"])

if __name__ == "__main__":
    main()
