import asyncio
import json
import re
import random
import shutil
import zipfile
import os
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import List, Dict, Any, Optional

import pandas as pd
from aiogram import Bot, Dispatcher, F
from aiogram.filters import Command
from aiogram.types import Message
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import StatesGroup, State
from aiogram.enums import ParseMode
from aiogram.utils.markdown import hcode, hbold

from dotenv import load_dotenv
from playwright.async_api import async_playwright, TimeoutError as PWTimeout

# ---------------------------------------------------------------------------
# ENV
# ---------------------------------------------------------------------------
load_dotenv()
BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()  # в .env значение BOT_TOKEN=...

# ---------------------------------------------------------------------------
# CONFIG / CONSTANTS
# ---------------------------------------------------------------------------
URL = "https://datahubdashboard.idsnext.live"
MENU_ITEM = "Bookings from Channels to (FN & FX)"

API_BASE = "https://idsdatahubdashboardapi.azurewebsites.net"
CM_CODE  = "CM1000"

SAVE_DIR = Path("xml_api")     # сюда складываются xml и итоговые Excel
RUN_DIR  = Path("work_runs")   # временная папка для архива/промежутка
SAVE_DIR.mkdir(exist_ok=True)
RUN_DIR.mkdir(exist_ok=True)

# скорость/поведение
CONCURRENCY       = 20           # количество одновременных запросов XML
REQ_TIMEOUT_MS    = 60_000
RETRY_ATTEMPTS    = 3
RETRY_BASE_DELAY  = 0.6
RETRY_JITTER      = 0.25

WRITERS             = 6
WRITE_QUEUE_MAXSIZE = 6000

# ---------------------------------------------------------------------------
# FSM состояния бота
# ---------------------------------------------------------------------------
class Form(StatesGroup):
    login = State()
    password = State()
    date_from = State()
    date_to = State()

# ---------------------------------------------------------------------------
# Утилиты — очистка, безопасное имя, упаковка zip
# ---------------------------------------------------------------------------
def clean_dirs():
    for p in [SAVE_DIR, RUN_DIR]:
        if p.exists():
            shutil.rmtree(p, ignore_errors=True)
        p.mkdir(exist_ok=True)

def _safe_filename(name: str) -> str:
    return re.sub(r'[\\/*?:"<>|]+', "_", name).strip()

def pack_zip(source_dir: Path, zip_path: Path):
    with zipfile.ZipFile(zip_path, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        for root, _, files in os.walk(source_dir):
            for f in files:
                full = Path(root) / f
                rel  = full.relative_to(source_dir)
                zf.write(full, arcname=str(rel))

# ---------------------------------------------------------------------------
# Playwright: логин, навигация, чтение отелей
# ---------------------------------------------------------------------------
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

    # password
    pass_inp = None
    for sel in ["css=input[type='password']", "css=input[aria-label*='Password' i]"]:
        loc = page.locator(sel).first
        try:
            await loc.wait_for(state="visible", timeout=4000)
            pass_inp = loc; break
        except Exception:
            continue
    if not pass_inp:
        raise RuntimeError("Не нашёл поле Password")

    async def robust_fill(inp_loc, value):
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

    await robust_fill(email_inp, username)
    await robust_fill(pass_inp, password)

    # submit
    clicked = False
    for sel in ["css=button[type=submit]",
                "css=button:has-text('Login')",
                "xpath=//button[normalize-space()='Login' or contains(.,'Login')]"]:
        try:
            await page.locator(sel).first.click(timeout=2000)
            clicked = True; break
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
        try:
            await email_inp.wait_for(state="detached", timeout=5000)
        except Exception:
            pass

    await page.wait_for_load_state("networkidle", timeout=30000)

async def open_menu_and_go(page, item_text: str):
    try:
        await page.mouse.click(28, 96); await asyncio.sleep(0.1)
    except Exception:
        pass

    for sel in ["i.fa-bars", "button:has(i.fa-bars)", "[aria-label*=menu i]", "button.mat-icon-button"]:
        try:
            await page.locator(sel).first.click(timeout=800)
            await asyncio.sleep(0.1); break
        except Exception:
            continue

    for sel in ["xpath=//*[self::a or self::button or self::div][normalize-space()='Bookings']",
                "text=Bookings"]:
        try:
            el = page.locator(sel).first
            if await el.is_visible():
                await el.scroll_into_view_if_needed(); await el.click(timeout=2000)
                break
        except Exception:
            continue

    target = [
        f"text={item_text}",
        "xpath=//*[self::a or self::button or self::div][contains(normalize-space(.), 'Bookings from Channels to (FN & FX)')]",
        "xpath=//*[contains(normalize-space(.), 'Bookings from Channels to') and contains(.,'(FN & FX)')]"
    ]
    clicked = False
    for sel in target:
        try:
            el = page.locator(sel).first
            if await el.is_visible():
                await el.scroll_into_view_if_needed(); await el.click(timeout=4000)
                clicked = True; break
        except Exception:
            continue
    if not clicked:
        raise RuntimeError("Не нашёл/не кликнул подпункт.")

    # проверяем заголовок
    ok = False
    for sel in ["text=Bookings from Channels to (FN & FX)",
                "xpath=//*[self::h1 or self::h2 or self::h3][contains(.,'Bookings from Channels to (FN & FX)')]"]:
        try:
            await page.locator(sel).first.wait_for(state="visible", timeout=8000)
            ok = True; break
        except Exception:
            continue
    if not ok:
        raise RuntimeError("Переход не подтвердился (нет заголовка).")

async def open_property_dropdown(page):
    opener = None
    for sel in [
        "xpath=//ngc-multiselect-dropdown//div[contains(@class,'dropdown-btn')][.//span[contains(normalize-space(),'Select Property')]]",
        "xpath=//*[contains(@class,'multiselect-dropdown')]//div[contains(@class,'dropdown-btn')][.//span[contains(normalize-space(),'Select Property')]]",
    ]:
        loc = page.locator(sel).first
        try:
            await loc.wait_for(state="visible", timeout=2500)
            opener = loc; break
        except Exception:
            continue

    if not opener:
        for sel in ["css=ngc-multiselect-dropdown .dropdown-btn", "css=.multiselect-dropdown .dropdown-btn"]:
            loc = page.locator(sel).first
            try:
                await loc.wait_for(state="visible", timeout=1500)
                opener = loc; break
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

def extract_pms_from_label(label: str) -> Optional[int]:
    head = label.split("-", 1)[0].strip()
    try:
        return int(head)
    except Exception:
        return None

# ---------------------------------------------------------------------------
# HTTP POST helper with retry
# ---------------------------------------------------------------------------
async def post_json_with_retry(req, url: str, payload: dict, *,
                               attempts: int = RETRY_ATTEMPTS,
                               timeout_ms: int = REQ_TIMEOUT_MS):
    delay = RETRY_BASE_DELAY
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
            body_text = await resp.text()
            if 200 <= status < 400:
                try:
                    return await resp.json()
                except Exception:
                    try:
                        return json.loads(body_text)
                    except Exception:
                        return body_text
            last_err = f"HTTP {status}: {body_text[:300]}"
        except PWTimeout as te:
            last_err = f"Timeout: {te}"
        except Exception as e:
            last_err = f"Exception: {e}"

        if i < attempts:
            jitter = random.uniform(0, RETRY_JITTER)
            await asyncio.sleep(delay + jitter)
            delay *= 2

    print(f"[ERROR] POST {url} failed after {attempts} attempts: {last_err}")
    return None

# ---------------------------------------------------------------------------
# API methods
# ---------------------------------------------------------------------------
async def api_is_bookinglog_ctx(req, pmscode: int, from_date: str, to_date: str, cmcode: str):
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
    js = await post_json_with_retry(req, url, payload)
    return js if isinstance(js, list) else []

async def api_get_xml_ctx(req, pmscode: int, token: int, cmcode: str, xml_type: str = "ReceivedXML") -> str:
    url = f"{API_BASE}/api/AriXml/IsAriBookXml"
    payload = {"pmscode": pmscode, "cmcode": cmcode, "token": token, "Type": xml_type}
    js = await post_json_with_retry(req, url, payload)
    if isinstance(js, dict):
        x = js.get("xmlData") or ""
        return x if isinstance(x, str) else ""
    if isinstance(js, list) and js:
        first = js[0]
        if isinstance(first, dict):
            x = first.get("xmlData") or ""
            return x if isinstance(x, str) else ""
    if isinstance(js, str):
        return js
    return ""

# ---------------------------------------------------------------------------
# Писатели
# ---------------------------------------------------------------------------
async def writer_worker(queue: asyncio.Queue):
    while True:
        item = await queue.get()
        if item is None:
            queue.task_done(); break
        pms, token, xml = item
        try:
            dir_ = SAVE_DIR / str(pms)
            dir_.mkdir(parents=True, exist_ok=True)
            path = dir_ / f"{pms}_{token}.xml"
            path.write_text(xml, encoding="utf-8")
        except Exception:
            pass
        finally:
            queue.task_done()

async def _fetch_single_xml_ctx(req, pms: int, token: int, sem: asyncio.Semaphore, write_queue: asyncio.Queue) -> bool:
    async with sem:
        try:
            xml = await api_get_xml_ctx(req, pms, token, CM_CODE, "ReceivedXML")
            if not xml:
                return False
            await write_queue.put((pms, token, xml))
            return True
        except Exception:
            return False

async def fetch_xml_for_pms_ctx(req, pms: int, from_date: str, to_date: str,
                                sem: asyncio.Semaphore, write_queue: asyncio.Queue) -> int:
    try:
        booking_log = await api_is_bookinglog_ctx(req, pms, from_date, to_date, CM_CODE)
        if not booking_log:
            print(f"[{pms}] нет записей")
            return 0

        tasks = []
        for row in booking_log:
            token_raw = row.get("echoToken")
            try:
                token = int(float(token_raw))
            except Exception:
                token = 0
            if token:
                tasks.append(_fetch_single_xml_ctx(req, pms, token, sem, write_queue))

        if not tasks:
            print(f"[{pms}] нет токенов")
            return 0

        result = await asyncio.gather(*tasks, return_exceptions=True)
        saved = sum(1 for r in result if isinstance(r, bool) and r)
        print(f"[{pms}] сохранено: {saved}/{len(tasks)}")
        return saved

    except Exception as e:
        print(f"[{pms}] ERROR: {e}")
        return 0

# ---------------------------------------------------------------------------
# XML parse + Excel builder
# ---------------------------------------------------------------------------
def parse_booking_info(xml_text: str) -> dict:
    """
    возвращает:
      start,end,given,surname,phone,email, price,currency
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
    def findtext(path: str)->str:
        el = root.find(path, ns)
        return (el.text or "").strip() if el is not None and el.text else ""

    ts = root.find(".//ota:TimeSpan", ns)
    start = (ts.attrib.get("Start","") if ts is not None else "").strip()
    end   = (ts.attrib.get("End","")   if ts is not None else "").strip()

    given   = findtext(".//ota:GivenName")
    surname = findtext(".//ota:Surname")
    email   = findtext(".//ota:Email")

    phone = ""
    pe = root.find(".//ota:Telephone", ns)
    if pe is not None:
        phone = (pe.attrib.get("PhoneNumber","") or "").strip()

    # Цена/валюта (Total)
    total = root.find(".//ota:Total", ns)
    price = ""
    currency = ""
    if total is not None and isinstance(total.attrib, dict):
        price = total.attrib.get("AmountIncludingMarkup") or total.attrib.get("AmountBeforeTax") or ""
        currency = total.attrib.get("CurrencyCode", "") or ""

    return {
        "start": start, "end": end,
        "given": given, "surname": surname,
        "phone": phone, "email": email,
        "price": price, "currency": currency,
    }

def write_hotel_excel(hotel_name: str, rows: list[dict], out_dir: Path) -> Path:
    out_dir.mkdir(parents=True, exist_ok=True)
    fn = _safe_filename(hotel_name) + ".xlsx"
    path = out_dir / fn

    df = pd.DataFrame(rows)
    df = df.rename(columns={
        "end":"Departure","start":"Arrival","given":"GivenName","surname":"Surname",
        "phone":"Phone","email":"Email","price":"Price","currency":"Currency"
    })
    cols = ["Departure","Arrival","GivenName","Surname","Phone","Email","Price","Currency"]
    for c in cols:
        if c not in df.columns:
            df[c] = ""
    df = df[cols]
    df.to_excel(path, index=False)
    return path

def build_hotel_reports(pms_to_name: dict[int, str], base_dir: Path = SAVE_DIR):
    """
    Возвращает (список путей, total_phones, total_emails)
    """
    out_paths = []
    total_phones = 0
    total_emails = 0

    for pms, hotel_name in pms_to_name.items():
        pms_dir = base_dir / str(pms)
        if not pms_dir.exists():
            continue

        rows = []
        for xml_path in sorted(pms_dir.glob("*.xml")):
            try:
                xml_text = xml_path.read_text(encoding="utf-8", errors="ignore")
                row = parse_booking_info(xml_text)
                if any(row.values()):
                    rows.append(row)
            except Exception:
                pass

        if rows:
            # подсчёт статистики по непустым полям
            df = pd.DataFrame(rows)
            phones = (df.get("phone","").astype(str).str.strip() != "").sum()
            emails = (df.get("email","").astype(str).str.strip() != "").sum()
            total_phones += int(phones)
            total_emails += int(emails)

            out = write_hotel_excel(hotel_name, rows, base_dir)
            out_paths.append(out)

    return out_paths, total_phones, total_emails

# ---------------------------------------------------------------------------
# TELEGRAM BOT
# ---------------------------------------------------------------------------
bot = Bot(BOT_TOKEN, parse_mode=ParseMode.HTML)
dp = Dispatcher()

@dp.message(Command("start"))
async def cmd_start(m: Message, state: FSMContext):
    await state.clear()
    await m.answer("Добро пожаловать!\nВведите логин (email):")
    await state.set_state(Form.login)

@dp.message(Form.login)
async def get_login(m: Message, state: FSMContext):
    await state.update_data(login=m.text.strip())
    await m.answer("Теперь введите пароль:")
    await state.set_state(Form.password)

@dp.message(Form.password)
async def get_password(m: Message, state: FSMContext):
    await state.update_data(password=m.text.strip())
    await m.answer("Укажите дату ОТ (формат YYYY-MM-DD):")
    await state.set_state(Form.date_from)

@dp.message(Form.date_from)
async def get_from(m: Message, state: FSMContext):
    await state.update_data(date_from=m.text.strip())
    await m.answer("Укажите дату ДО (формат YYYY-MM-DD):")
    await state.set_state(Form.date_to)

@dp.message(Form.date_to)
async def get_to(m: Message, state: FSMContext):
    data = await state.get_data()
    username = data.get("login","")
    password = data.get("password","")
    date_from = data.get("date_from","").strip()
    date_to   = m.text.strip()

    # — очистка предыдущих run-файлов
    clean_dirs()
    await m.answer("Стартую проверку логина/пароля и получение списка отелей...")

    # основной процесс
    try:
        async with async_playwright() as p:
            browser = await p.chromium.launch(
                headless=True,
                args=["--no-sandbox", "--disable-dev-shm-usage",
                      "--disable-gpu", "--disable-extensions",
                      "--disable-background-timer-throttling",
                      "--disable-renderer-backgrounding"],
            )
            context = await browser.new_context()

            # блокируем лишние ресурсы
            async def route_handler(route, request):
                rtype = request.resource_type
                url = request.url
                if rtype in ("image", "font", "stylesheet"):
                    await route.abort(); return
                if any(x in url for x in ["analytics","googletag","hotjar","fonts.googleapis"]):
                    await route.abort(); return
                await route.continue_()
            await context.route("**/*", route_handler)

            page = await context.new_page()

            await do_login(page, username, password)
            await m.answer("Авторизация прошла, захожу в раздел 'Bookings from Channels...'")
            await open_menu_and_go(page, MENU_ITEM)

            labels = await list_hotels_from_dropdown(page)
            pms_list: List[int] = []
            pms_to_name: dict[int, str] = {}
            for txt in labels:
                p = extract_pms_from_label(txt)
                if p:
                    pms_list.append(p)
                    pms_to_name[p] = txt.split("-",1)[-1].strip()

            pms_list = sorted(set(pms_list))
            await m.answer(f"Нашёл {len(pms_list)} отелей. Начинаю загрузку XML за {date_from} → {date_to}")

            req = context.request
            sem = asyncio.Semaphore(CONCURRENCY)

            write_queue = asyncio.Queue(maxsize=WRITE_QUEUE_MAXSIZE)
            writer_tasks = [asyncio.create_task(writer_worker(write_queue)) for _ in range(WRITERS)]

            total_saved = 0
            # без батчей — запускаем сразу все
            tasks = [fetch_xml_for_pms_ctx(req, p, date_from, date_to, sem, write_queue) for p in pms_list]
            for chunk in asyncio.as_completed(tasks):
                res = await chunk
                total_saved += res

            for _ in range(WRITERS):
                await write_queue.put(None)
            await write_queue.join()
            await asyncio.gather(*writer_tasks, return_exceptions=True)

            await m.answer(f"XML загружены: {total_saved}. Формирую Excel...")

            report_paths, tot_phones, tot_emails = build_hotel_reports(pms_to_name, SAVE_DIR)
            await m.answer(f"Готово: сформировано {len(report_paths)} Excel-файлов.\n"
                           f"Телефонов: {tot_phones}\n"
                           f"Email: {tot_emails}")

            # упаковываем в zip
            zip_path = RUN_DIR / "reports.zip"
            pack_zip(SAVE_DIR, zip_path)

            await m.answer_document(document=zip_path.open("rb"), caption="Отчёты в архиве (ZIP)")

            await browser.close()

    except Exception as e:
        await m.answer(f"⚠️ Ошибка: {hcode(str(e))}")

    await state.clear()

# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------
def main():
    if not BOT_TOKEN:
        raise RuntimeError("BOT_TOKEN пуст. Укажите его в .env (BOT_TOKEN=XXXXXXXX)")
    asyncio.run(dp.start_polling(bot))

if __name__ == "__main__":
    main()
