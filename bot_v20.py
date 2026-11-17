"""
Bulk Channel Forward Bot
------------------------
Copies a range of messages (videos, PDFs, text) from a source channel to a
target channel in their original order and publishes a topic index. It can also
build an index for an existing batch and bulk-delete a range of messages.

Commands (admins, private chat):
    /forward -> forward the FIRST and LAST message of the range from the source
                channel, then any message from the target channel -> confirm.
    /mixforward -> like /forward, but the range is forwarded in the order of the number
                each caption starts with (for sources uploaded out of order).
    /live    -> forward the message to start from (source) and one message of the
                target channel; the bot then forwards every new post as it arrives.
                Tap "Forward Complete" in the task panel to build the index.
    /index   -> forward the FIRST and LAST message of an existing batch, choose
                where the index goes (same channel or another) -> confirm.
    /delete  -> forward the FIRST and LAST message of a range -> confirm -> the
                bot deletes every message in between.
    /txt_checker -> forward the FIRST and LAST message of an old batch, then send a
                new TXT of links; the bot removes what is already uploaded in the
                channel and returns a TXT with only the new links.
    /txt_update  -> send an OLD TXT and a NEW TXT; the bot returns a TXT with only the
                links that are not in the old one.
    /add_channel -> add channels for the schedule tools (any time, as often as needed).
    /daily_schedule -> create schedules: each posts one message to the channels you pick every
                day (the previous post is deleted and the message is posted again). Every
                schedule can be viewed, edited, re-timed, stopped or deleted on its own.
    /quick_schedule -> send a message to your channels right now (no schedule), with an undo.
    /schedules -> open the list of scheduled messages directly.
    /tasks   -> lists every task you have running (several can run at once).
    /stop    -> stops a running task (asks which one when there are several).

Admin management (owner only): /add <user_id>, /remove <user_id>, /admins

Index caption formats recognised:
    1) Package : <package name>
    2) Subject Name: <subject>  /  Topic Name: <topic>   (Subject Name alone also works)
    3) 🔖 Topic ➾ <topic name>
    4) Topic : <topic name>   /   Topic: <topic name>
    5) 🔖 Topic ➾ <topic>  +  🎦 Title ➾ (<short title>) <full lecture name>
       (only the bracketed part of the title is shown; a title without brackets
       is skipped and just the topic is indexed)
    6) 🏷️ <topic name>  |
"""

import asyncio
import difflib
import html
import itertools
import logging
import os
import random
import re
import secrets
import tempfile
import time
import unicodedata
from collections import Counter
from dataclasses import asdict, dataclass, field
from datetime import datetime, timedelta, timezone
from typing import Awaitable, Callable, Dict, List, Optional, Tuple
from zoneinfo import ZoneInfo

from motor.motor_asyncio import AsyncIOMotorClient
from pyrogram import Client, filters, idle, raw
from pyrogram.enums import ParseMode
from pyrogram.errors import FloodWait, RPCError
from pyrogram.types import (
    CallbackQuery,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    Message,
)

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------
API_ID = int(os.environ["API_ID"])
API_HASH = os.environ["API_HASH"]
BOT_TOKEN = os.environ["BOT_TOKEN"]
OWNER_ID = int(os.environ["OWNER_ID"])
MONGO_URI = os.environ["MONGO_URI"]
DB_NAME = os.getenv("DB_NAME", "forward_bot")

# True  -> posts appear without the "Forwarded from" header.
# False -> standard forwards with the original-channel header.
HIDE_FORWARD_TAG = os.getenv("HIDE_FORWARD_TAG", "true").lower() == "true"

BATCH_SIZE = 100            # Telegram allows up to 100 messages per forward call
MAX_RETRIES = 5             # retry attempts per API call (FloodWait included)
PROGRESS_INTERVAL = 3.0     # minimum seconds between progress edits
MAX_TASKS_PER_ADMIN = int(os.getenv("MAX_TASKS_PER_ADMIN", "5"))  # tasks one admin may run at once
MAX_TXT_BYTES = 20 * 1024 * 1024  # largest TXT file accepted
SCHEDULE_TIMEZONE = os.getenv("SCHEDULE_TIMEZONE", "Asia/Kolkata")  # time zone of /daily_schedule
SCHEDULER_TICK_SECONDS = 30   # how often due schedules are looked for
SCHEDULE_CONCURRENCY = 4      # channels posted to at the same time
LIVE_POLL_SECONDS = 20      # live mode: safety re-check when no new post is announced
LIVE_PANEL_INTERVAL = 5.0   # live mode: minimum seconds between control-panel refreshes
DEFAULT_PACKAGE = "General"
# "🎦 Title ➾ (Analog Electronics) Lec-53 ..." -> show "(Analog Electronics)" (True)
# or just "Analog Electronics" (False) in the index.
SHOW_TITLE_BRACKETS = False
INDEX_TITLE = "📂 <b>INDEX</b>"
MESSAGE_LIMIT = 3900        # safe size for a single Telegram message

logging.basicConfig(
    format="%(asctime)s | %(levelname)s | %(message)s", level=logging.INFO
)
logger = logging.getLogger("forward-bot")

app = Client(
    "forward_bot",
    api_id=API_ID,
    api_hash=API_HASH,
    bot_token=BOT_TOKEN,
    in_memory=True,  # Heroku's filesystem is ephemeral; no session file needed
)

# ---------------------------------------------------------------------------
# Persistence (admin list)
# ---------------------------------------------------------------------------
mongo = AsyncIOMotorClient(MONGO_URI)
admins_col = mongo[DB_NAME]["admins"]
channels_col = mongo[DB_NAME]["sched_channels"]   # channels added for /daily_schedule
schedules_col = mongo[DB_NAME]["schedules"]       # daily schedules
live_col = mongo[DB_NAME]["live_tasks"]  # state of running live tasks (survives restarts)


async def is_admin(user_id: int) -> bool:
    if user_id == OWNER_ID:
        return True
    return await admins_col.find_one({"_id": user_id}) is not None


async def _admin_check(_, __, update) -> bool:
    user = getattr(update, "from_user", None)
    return bool(user) and await is_admin(user.id)


admin_filter = filters.create(_admin_check)

# ---------------------------------------------------------------------------
# Session state
# ---------------------------------------------------------------------------
STEP_AWAIT_START = "await_start"
STEP_AWAIT_END = "await_end"
STEP_AWAIT_TARGET = "await_target"
STEP_AWAIT_CONFIRM = "await_confirm"
STEP_RUNNING = "running"
STEP_AWAIT_TXT = "await_txt"
STEP_DS_CHANNEL = "ds_channel"
STEP_DS_MESSAGE = "ds_message"
STEP_DS_SELECT = "ds_select"
STEP_DS_TIME = "ds_time"
STEP_DS_CONFIRM = "ds_confirm"
STEP_DS_EDIT = "ds_edit"
STEP_DS_EDIT_CHOICE = "ds_edit_choice"
STEP_QS_MESSAGE = "qs_message"
STEP_QS_CONFIRM = "qs_confirm"
STEP_QS_SELECT = "qs_select"
STEP_QS_EDIT = "qs_edit"
STEP_AWAIT_OLD_TXT = "await_old_txt"
STEP_AWAIT_NEW_TXT = "await_new_txt"

MODE_FORWARD = "forward"
MODE_DELETE = "delete"
MODE_INDEX = "index"
MODE_LIVE = "live"
MODE_MIX = "mix"
MODE_DAILY = "daily"
MODE_TXTCHECK = "txt_check"
MODE_TXTUPDATE = "txt_update"


@dataclass
class Session:
    mode: str = MODE_FORWARD
    step: str = STEP_AWAIT_START
    source_id: int = 0
    source_title: str = ""
    start_id: int = 0
    end_id: int = 0
    target_id: int = 0
    target_title: str = ""
    cancel: bool = False
    resume_doc: Optional[dict] = None  # saved live task being re-linked after a restart
    ds: dict = field(default_factory=dict)  # /daily_schedule wizard data
    txt_text: Optional[str] = None     # TXT received by /txt_checker or /txt_update
    txt_name: str = ""
    job_id: int = 0                    # set when the task starts running
    admin_id: int = 0


@dataclass
class IndexEntry:
    kind: str                # "package" or "subject" (caption format that was detected)
    title: str               # package name or subject name
    topic: Optional[str]     # topic name (subject format only)
    target_msg_id: int       # first message of this entry in the target channel


# (kind, title, topic) - identifies the section a message belongs to
SectionKey = Tuple[str, str, Optional[str]]


@dataclass
class LiveTask:
    """A running live-forwarding task (an admin can run several)."""
    task_id: str
    admin_id: int
    source_id: int
    source_title: str
    target_id: int
    target_title: str
    start_id: int
    next_id: int                                   # next source message ID to process
    entries: List[IndexEntry] = field(default_factory=list)
    current_key: SectionKey = ("package", DEFAULT_PACKAGE, None)
    forwarded: int = 0
    failed: List[int] = field(default_factory=list)
    latest_seen: int = 0                           # highest source ID announced by Telegram
    complete: bool = False                         # admin tapped "Forward Complete"
    stop: bool = False                             # admin asked to stop without an index
    status: Optional[Message] = None               # control-panel message
    wake: asyncio.Event = field(default_factory=asyncio.Event)

    def notify(self, msg_id: int) -> None:
        self.latest_seen = max(self.latest_seen, msg_id)
        self.wake.set()

    def to_doc(self) -> dict:
        return {
            "_id": self.task_id,
            "admin_id": self.admin_id,
            "source_id": self.source_id,
            "source_title": self.source_title,
            "target_id": self.target_id,
            "target_title": self.target_title,
            "start_id": self.start_id,
            "next_id": self.next_id,
            "forwarded": self.forwarded,
            "failed": self.failed,
            "entries": [asdict(entry) for entry in self.entries],
            "current_key": list(self.current_key),
        }

    @classmethod
    def from_doc(cls, doc: dict) -> "LiveTask":
        return cls(
            task_id=str(doc["_id"]),
            admin_id=doc.get("admin_id", doc["_id"]),
            source_id=doc["source_id"],
            source_title=doc["source_title"],
            target_id=doc["target_id"],
            target_title=doc["target_title"],
            start_id=doc["start_id"],
            next_id=doc["next_id"],
            forwarded=doc.get("forwarded", 0),
            failed=list(doc.get("failed", [])),
            entries=[IndexEntry(**entry) for entry in doc.get("entries", [])],
            current_key=tuple(doc.get("current_key", ["package", DEFAULT_PACKAGE, None])),
        )


sessions: Dict[int, Session] = {}
running_jobs: Dict[int, Session] = {}     # running forward / index / delete tasks, keyed by job ID
live_tasks: Dict[str, LiveTask] = {}      # running live tasks, keyed by task ID
paused_docs: Dict[str, dict] = {}         # saved live tasks waiting to be re-linked, keyed by task ID
background_tasks: set = set()
job_counter = itertools.count(1)


def register_job(session: Session, admin_id: int) -> None:
    """Move a confirmed wizard session into the registry of running tasks."""
    session.job_id = next(job_counter)
    session.admin_id = admin_id
    session.step = STEP_RUNNING
    running_jobs[session.job_id] = session
    sessions.pop(admin_id, None)


def count_admin_tasks(admin_id: int) -> int:
    jobs = sum(1 for job in running_jobs.values() if job.admin_id == admin_id)
    live = sum(1 for task in live_tasks.values() if task.admin_id == admin_id)
    return jobs + live

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------
PACKAGE_RE = re.compile(r"^\s*package\s*[:：]\s*(.+?)\s*$", re.IGNORECASE)
SUBJECT_RE = re.compile(r"^\s*subject\s*name\s*[:：]\s*(.+?)\s*$", re.IGNORECASE)
TOPIC_RE = re.compile(r"^\s*topic\s*name\s*[:：]\s*(.+?)\s*$", re.IGNORECASE)
# Topic-only formats: "🔖 Topic  ➾ GATE Hindi" and "Topic : NUMERICAL METHOD".
# Optional leading icon, the word "Topic", then any symbol separator (➾ : - → ...).
# "Topic Name:" never matches this.
TOPIC_ONLY_RE = re.compile(r"^\W*topic\s*[^\w\s]+\s*(.+?)\s*$", re.IGNORECASE)
# Tag line, e.g. "🏷️ Heat Transfer  |  ": a 🏷 icon followed by the name, ended by "|" or the line end.
TAG_RE = re.compile(r"^\s*\U0001F3F7\uFE0F?\s*([^|]+?)\s*(?:\|.*)?$")
# Title line, e.g. "🎦 Title  ➾ (Analog Electronics) Lec-53  MOSFET 1.mp4"
TITLE_RE = re.compile(r"^\W*title\s*[^\w\s]+\s*(.+?)\s*$", re.IGNORECASE)
# Same title line, but only with an icon-style separator (➾ → ...). A plain colon
# ("Title : name.mp4") is deliberately NOT matched: such a title never reaches the index.
TITLE_ICON_RE = re.compile(r"^\W*title\s*(?![:：])[^\w\s]+\s*(.+?)\s*$", re.IGNORECASE)
BRACKET_RE = re.compile(r"\(([^()]+)\)")


# Small-caps lookalikes (ᴀ ʙ ᴄ ...) are not folded by Unicode normalisation,
# so they are mapped to plain letters explicitly.
SMALL_CAPS = str.maketrans(
    "ᴀʙᴄᴅᴇꜰɢʜɪᴊᴋʟᴍɴᴏᴘǫʀꜱᴛᴜᴠᴡʏᴢ",   # small-caps letters (there is no common small-caps x)
    "abcdefghijklmnopqrstuvwyz",        # plain equivalents
)
SMALL_CAPS[ord("ғ")] = "f"  # common small-caps "f" substitute (Cyrillic ghe with stroke)


def normalize_line(line: str) -> str:
    """Fold fancy fonts (full-width, bold, small caps) to plain text for matching."""
    return unicodedata.normalize("NFKC", line).translate(SMALL_CAPS)


def clean_value(value: str) -> str:
    """Trim and collapse repeated spaces."""
    return " ".join(value.split())


def bracket_title(title: str) -> Optional[str]:
    """Return the bracketed part of a title, or None when it has no brackets.
    "(Analog Electronics) Lec-53 ..." -> "Analog Electronics"."""
    match = BRACKET_RE.search(title)
    if match and match.group(1).strip():
        inner = clean_value(match.group(1))
        return f"({inner})" if SHOW_TITLE_BRACKETS else inner
    return None


def get_forward_origin(message: Message) -> Optional[Tuple[object, int]]:
    """Return (chat, message_id) of the original channel post, if any.
    Supports both the classic and the newer Pyrogram forward attributes."""
    chat = getattr(message, "forward_from_chat", None)
    msg_id = getattr(message, "forward_from_message_id", None)
    if chat and msg_id:
        return chat, msg_id
    origin = getattr(message, "forward_origin", None)
    chat = getattr(origin, "chat", None)
    msg_id = getattr(origin, "message_id", None)
    if chat and msg_id:
        return chat, msg_id
    return None


def parse_metadata(text: str) -> Optional[SectionKey]:
    """Detect the caption format and return (kind, title, topic).

    Supported formats (in order of priority):
        Subject Name: <subject>  +  Topic Name: <topic>  -> ("subject", subject, topic)
        Package : <package>                              -> ("package", package, None)
        🔖 Topic ➾ <topic>  +  🎦 Title ➾ (<name>) ...   -> ("subject", topic, name)
        🔖 Topic ➾ <topic>  /  Topic : <topic>           -> ("subject", topic, None)
        🏷️ <topic>  |                                    -> ("subject", topic, None)
    Fancy fonts (small caps, bold, full-width) are folded to plain text first."""
    subject = topic = package = topic_only = title = tag = None
    for line in (text or "").splitlines():
        line = normalize_line(line)
        if match := SUBJECT_RE.match(line):
            subject = clean_value(match.group(1))
        elif match := TOPIC_RE.match(line):
            topic = clean_value(match.group(1))
        elif match := PACKAGE_RE.match(line):
            package = clean_value(match.group(1))
        elif match := TOPIC_ONLY_RE.match(line):
            topic_only = clean_value(match.group(1))
        elif match := TITLE_ICON_RE.match(line):
            title = clean_value(match.group(1))
        elif match := TAG_RE.match(line):
            tag = clean_value(match.group(1))
    if subject:
        return "subject", subject, topic
    if package:
        return "package", package, None
    heading = topic_only or tag
    if heading:
        # Only a bracketed title gets its own line under the topic; without
        # brackets just the topic itself is indexed.
        return "subject", heading, (bracket_title(title) if title else None)
    return None


def message_link(chat, msg_id: int) -> str:
    if getattr(chat, "username", None):
        return f"https://t.me/{chat.username}/{msg_id}"
    internal_id = str(chat.id)
    internal_id = internal_id[4:] if internal_id.startswith("-100") else internal_id.lstrip("-")
    return f"https://t.me/c/{internal_id}/{msg_id}"


def build_index_pages(entries: List[IndexEntry], target_chat) -> List[str]:
    """Render the index.

    Subject format  : numbered subject name, followed by its topics (each a link
                      to the first message of that topic).
    Package / Topic : numbered name, followed by an Index link.
    Long lists are split into Telegram-sized pages; a subject that spills over
    to the next page repeats its heading marked "(contd.)"."""
    groups: List[Tuple[str, List[str]]] = []
    previous: Optional[Tuple[str, str]] = None
    number = 0

    for entry in entries:
        url = message_link(target_chat, entry.target_msg_id)
        index_link = f'📑 <a href="{url}">Index</a>'
        group_key = (entry.kind, entry.title)

        # Consecutive entries of the same subject share one heading.
        if entry.kind == "subject" and group_key == previous:
            line = f'▫️ <a href="{url}">{html.escape(entry.topic)}</a>' if entry.topic else index_link
            groups[-1][1].append(line)
        else:
            number += 1
            heading = f"<b>{number:02d}. {html.escape(entry.title)}</b>"
            if entry.kind == "subject" and entry.topic:
                line = f'▫️ <a href="{url}">{html.escape(entry.topic)}</a>'
            else:
                line = index_link
            groups.append((heading, [line]))
        previous = group_key

    pages: List[str] = []
    buffer = INDEX_TITLE
    for heading, lines in groups:
        shown = False       # heading already written on the current page
        continued = False   # group has spilled over from a previous page
        for line in lines:
            head = f"{heading} <i>(contd.)</i>" if continued else heading
            cost = len(line) + 1 + (0 if shown else len(head) + 2)
            if buffer and len(buffer) + cost > MESSAGE_LIMIT:
                pages.append(buffer)
                buffer, shown, continued = "", False, True
                head = f"{heading} <i>(contd.)</i>"
            if not shown:
                buffer += ("\n\n" if buffer else "") + head
                shown = True
            buffer += "\n" + line
    if buffer:
        pages.append(buffer)
    return pages


async def with_retry(factory: Callable[[], Awaitable]):
    """Run an API call, honouring FloodWait and retrying transient failures."""
    for attempt in range(1, MAX_RETRIES + 1):
        try:
            return await factory()
        except FloodWait as exc:
            logger.warning("FloodWait: sleeping %ss", exc.value)
            await asyncio.sleep(exc.value + 1)
        except RPCError:
            if attempt == MAX_RETRIES:
                raise
            await asyncio.sleep(2 * attempt)
    raise RuntimeError("Retry limit exceeded")


async def safe_edit(message: Message, text: str, **kwargs) -> None:
    try:
        await message.edit_text(text, **kwargs)
    except FloodWait as exc:
        await asyncio.sleep(exc.value)
    except RPCError:
        pass


def format_ids(ids: List[int], limit: int = 40) -> str:
    shown = ", ".join(str(i) for i in ids[:limit])
    extra = f" … (+{len(ids) - limit} more)" if len(ids) > limit else ""
    return shown + extra


def update_entries(
    entries: List[IndexEntry], current_key: SectionKey, message: Message, msg_id: int
) -> SectionKey:
    """Register a message in the index. A new entry starts only when the section
    changes; it links to the first message of that section. Messages without a
    recognisable caption stay in the current section."""
    # Media carries the format in its caption; text-only messages carry it in the text.
    key = parse_metadata(message.caption or message.text or "") or current_key
    # A subject/topic without a bracketed title stays in the current section
    # when the subject itself has not changed.
    if key[0] == "subject" and key[2] is None and current_key[:2] == key[:2]:
        key = current_key
    if key != current_key or not entries:
        entries.append(IndexEntry(*key, msg_id))
    return key


async def post_index_pages(client: Client, chat_id: int, pages: List[str]) -> None:
    for page in pages:
        await with_retry(
            lambda page=page: client.send_message(
                chat_id, page,
                parse_mode=ParseMode.HTML,
                disable_web_page_preview=True,
            )
        )


# ---------------------------------------------------------------------------
# Forwarding engine
# ---------------------------------------------------------------------------
async def forward_batch(
    client: Client,
    source_peer,
    target_peer,
    source_id: int,
    target_id: int,
    ids: List[int],
) -> Tuple[Dict[int, int], List[int]]:
    """Forward up to 100 messages in a single request (server-side, in order).

    Returns (mapping of source id -> new target id, ids that could not be delivered).
    Anything the bulk call does not deliver is retried one by one."""
    delivered: Dict[int, int] = {}
    random_ids = [random.getrandbits(63) for _ in ids]

    try:
        result = await with_retry(
            lambda: client.invoke(
                raw.functions.messages.ForwardMessages(
                    from_peer=source_peer,
                    id=ids,
                    random_id=random_ids,
                    to_peer=target_peer,
                    drop_author=HIDE_FORWARD_TAG,
                )
            )
        )
        id_map = {
            upd.random_id: upd.id
            for upd in getattr(result, "updates", [])
            if isinstance(upd, raw.types.UpdateMessageID)
        }
        for sid, rid in zip(ids, random_ids):
            if rid in id_map:
                delivered[sid] = id_map[rid]
    except RPCError as exc:
        logger.warning("Bulk forward failed (%s); falling back to per-message mode", exc)

    failed: List[int] = []
    for sid in (i for i in ids if i not in delivered):
        try:
            if HIDE_FORWARD_TAG:
                sent = await with_retry(lambda sid=sid: client.copy_message(target_id, source_id, sid))
            else:
                sent = await with_retry(lambda sid=sid: client.forward_messages(target_id, source_id, sid))
            delivered[sid] = sent.id
        except RPCError as exc:
            logger.error("Message %s could not be forwarded: %s", sid, exc)
            failed.append(sid)
    return delivered, failed


async def run_job(client: Client, admin_id: int, session: Session, status: Message) -> None:
    started = time.monotonic()
    ids = list(range(session.start_id, session.end_id + 1))
    total = len(ids)
    entries: List[IndexEntry] = []
    skipped: List[int] = []
    failed: List[int] = []
    forwarded_count = 0
    scanned = 0
    current_key: SectionKey = ("package", DEFAULT_PACKAGE, None)
    last_edit = 0.0

    try:
        source_peer = await client.resolve_peer(session.source_id)
        target_peer = await client.resolve_peer(session.target_id)
        target_chat = await client.get_chat(session.target_id)

        for offset in range(0, total, BATCH_SIZE):
            if session.cancel:
                break
            chunk_ids = ids[offset: offset + BATCH_SIZE]
            fetched = await with_retry(lambda: client.get_messages(session.source_id, chunk_ids))
            if not isinstance(fetched, list):
                fetched = [fetched]

            deliverable: List[Message] = []
            for sid, msg in zip(chunk_ids, fetched):
                if msg is None or msg.empty or msg.service:
                    skipped.append(sid)
                else:
                    deliverable.append(msg)

            if deliverable:
                mapping, missing = await forward_batch(
                    client, source_peer, target_peer,
                    session.source_id, session.target_id,
                    [m.id for m in deliverable],
                )
                failed.extend(missing)
                for msg in deliverable:
                    new_id = mapping.get(msg.id)
                    if new_id is None:
                        continue
                    forwarded_count += 1
                    current_key = update_entries(entries, current_key, msg, new_id)

            scanned += len(chunk_ids)
            if time.monotonic() - last_edit >= PROGRESS_INTERVAL:
                last_edit = time.monotonic()
                await safe_edit(
                    status,
                    f"⏳ <b>Forwarding in progress</b>\n\n"
                    f"Processed: <code>{scanned}/{total}</code>\n"
                    f"Forwarded: <code>{forwarded_count}</code>",
                    parse_mode=ParseMode.HTML,
                )

        index_posted = False
        if not session.cancel and entries:
            await safe_edit(status, "🗂 Building the index…")
            await post_index_pages(
                client, session.target_id, build_index_pages(entries, target_chat)
            )
            index_posted = True

        elapsed = int(time.monotonic() - started)
        report = [
            "🛑 <b>Job cancelled</b>" if session.cancel else "✅ <b>Job completed</b>",
            "",
            f"Range: <code>{session.start_id} → {session.end_id}</code>",
            f"Forwarded: <code>{forwarded_count}</code>",
            f"Index entries: <code>{len(entries)}</code> "
            f"({'posted' if index_posted else 'not posted'})",
            f"Time taken: <code>{elapsed}s</code>",
        ]
        if skipped:
            report.append(f"\nSkipped (deleted/service) IDs:\n<code>{format_ids(skipped)}</code>")
        if failed:
            report.append(f"\n⚠️ Failed IDs:\n<code>{format_ids(failed)}</code>")
        await safe_edit(status, "\n".join(report), parse_mode=ParseMode.HTML)

    except Exception as exc:  # noqa: BLE001 - surface any failure to the admin
        logger.exception("Job failed")
        await safe_edit(
            status,
            f"❌ <b>Job failed</b>\n\n<code>{html.escape(str(exc))}</code>\n\n"
            "Make sure the bot is an admin in both channels.",
            parse_mode=ParseMode.HTML,
        )
    finally:
        running_jobs.pop(session.job_id, None)


# ---------------------------------------------------------------------------
# Mix forward engine (sequence by the leading caption number)
# ---------------------------------------------------------------------------
LEADING_NUMBER_RE = re.compile(r"^\W*(\d+)(?!\w)")
MISSING_NUMBERS_SCAN_LIMIT = 20_000


def leading_number(message: Message) -> Optional[int]:
    """The number a caption (or text) starts with: "662. CLASS 02" -> 662.
    A caption such as "2nd Aug ..." has no serial number and returns None."""
    text = normalize_line((message.caption or message.text or "")[:80])
    match = LEADING_NUMBER_RE.match(text)
    return int(match.group(1)) if match else None


def order_by_number(messages: List[Message]) -> Tuple[List[Message], List[int], int]:
    """Sort messages by their leading number.

    A message without a number stays with the numbered message that precedes it
    in the source channel, so text and notes keep their place. Equal numbers keep
    their source order. Returns (ordered messages, numbers found, unnumbered count)."""
    blocks: List[list] = []  # [number or None, first source ID, [messages]]
    numbers: List[int] = []
    unnumbered = 0
    for msg in sorted(messages, key=lambda m: m.id):
        number = leading_number(msg)
        if number is not None:
            numbers.append(number)
            blocks.append([number, msg.id, [msg]])
        elif blocks:
            blocks[-1][2].append(msg)
            unnumbered += 1
        else:  # before the first numbered message
            blocks.append([None, msg.id, [msg]])
            unnumbered += 1
    blocks.sort(key=lambda block: (-1 if block[0] is None else block[0], block[1]))
    return [msg for block in blocks for msg in block[2]], numbers, unnumbered


def split_into_runs(ordered_ids: List[int], limit: int = BATCH_SIZE) -> List[List[int]]:
    """Cut the wanted order into runs whose source IDs only increase.

    A run is forwarded in a single call, and increasing IDs keep their order for
    certain. The runs are sent one after another, so the wanted order is kept."""
    runs: List[List[int]] = []
    current: List[int] = []
    for source_id in ordered_ids:
        if current and (source_id < current[-1] or len(current) >= limit):
            runs.append(current)
            current = []
        current.append(source_id)
    if current:
        runs.append(current)
    return runs


def number_gaps(numbers: List[int]) -> Tuple[List[int], List[int]]:
    """Numbers missing between the smallest and the largest, and numbers used twice."""
    if not numbers:
        return [], []
    counts = Counter(numbers)
    duplicates = sorted(n for n, c in counts.items() if c > 1)
    low, high = min(counts), max(counts)
    missing = [n for n in range(low, high + 1) if n not in counts] if high - low <= MISSING_NUMBERS_SCAN_LIMIT else []
    return missing, duplicates


async def run_mix_job(client: Client, admin_id: int, session: Session, status: Message) -> None:
    started = time.monotonic()
    ids = list(range(session.start_id, session.end_id + 1))
    total = len(ids)
    deliverable: List[Message] = []
    skipped: List[int] = []
    failed: List[int] = []
    entries: List[IndexEntry] = []
    current_key: SectionKey = ("package", DEFAULT_PACKAGE, None)
    forwarded_count = 0
    last_edit = 0.0

    try:
        source_peer = await client.resolve_peer(session.source_id)
        target_peer = await client.resolve_peer(session.target_id)
        target_chat = await client.get_chat(session.target_id)

        # Phase 1: read every message of the range.
        for offset in range(0, total, BATCH_SIZE):
            if session.cancel:
                break
            chunk_ids = ids[offset: offset + BATCH_SIZE]
            fetched = await with_retry(lambda: client.get_messages(session.source_id, chunk_ids))
            if not isinstance(fetched, list):
                fetched = [fetched]
            for sid, msg in zip(chunk_ids, fetched):
                if msg is None or msg.empty or msg.service:
                    skipped.append(sid)
                else:
                    deliverable.append(msg)
            if time.monotonic() - last_edit >= PROGRESS_INTERVAL:
                last_edit = time.monotonic()
                await safe_edit(
                    status,
                    f"📖 <b>Reading the range</b>\n\nRead: <code>{min(offset + BATCH_SIZE, total)}/{total}</code>",
                    parse_mode=ParseMode.HTML,
                )

        # Phase 2: arrange by number and forward run by run.
        ordered, numbers, unnumbered = order_by_number(deliverable)
        by_id = {msg.id: msg for msg in ordered}
        runs = split_into_runs([msg.id for msg in ordered])

        for run in runs:
            if session.cancel:
                break
            mapping, missing = await forward_batch(
                client, source_peer, target_peer, session.source_id, session.target_id, run
            )
            failed.extend(missing)
            for source_id in run:
                new_id = mapping.get(source_id)
                if new_id is None:
                    continue
                forwarded_count += 1
                current_key = update_entries(entries, current_key, by_id[source_id], new_id)
            if time.monotonic() - last_edit >= PROGRESS_INTERVAL:
                last_edit = time.monotonic()
                await safe_edit(
                    status,
                    f"⏳ <b>Forwarding in number order</b>\n\n"
                    f"Forwarded: <code>{forwarded_count}/{len(ordered)}</code>",
                    parse_mode=ParseMode.HTML,
                )

        index_posted = False
        if not session.cancel and entries:
            await safe_edit(status, "🗂 Building the index…")
            await post_index_pages(client, session.target_id, build_index_pages(entries, target_chat))
            index_posted = True

        missing_numbers, repeated = number_gaps(numbers)
        report = [
            "🛑 <b>Mix forward stopped</b>" if session.cancel else "✅ <b>Mix forward completed</b>",
            "",
            f"Range: <code>{session.start_id} → {session.end_id}</code>",
            f"Forwarded: <code>{forwarded_count}</code> in <code>{len(runs)}</code> calls",
            f"Index entries: <code>{len(entries)}</code> ({'posted' if index_posted else 'not posted'})",
            f"Time taken: <code>{int(time.monotonic() - started)}s</code>",
        ]
        if unnumbered:
            report.append(f"Messages without a number (kept after the previous number): <code>{unnumbered}</code>")
        if missing_numbers:
            report.append(f"\n🔎 Missing numbers:\n<code>{format_ids(missing_numbers)}</code>")
        if repeated:
            report.append(f"\n🔁 Numbers used more than once:\n<code>{format_ids(repeated)}</code>")
        if skipped:
            report.append(f"\nSkipped (deleted/service) IDs:\n<code>{format_ids(skipped)}</code>")
        if failed:
            report.append(f"\n⚠️ Failed IDs:\n<code>{format_ids(failed)}</code>")
        await safe_edit(status, "\n".join(report), parse_mode=ParseMode.HTML)

    except Exception as exc:  # noqa: BLE001 - surface any failure to the admin
        logger.exception("Mix forward failed")
        await safe_edit(
            status,
            f"❌ <b>Mix forward failed</b>\n\n<code>{html.escape(str(exc))}</code>\n\n"
            "Make sure the bot is an admin in both channels.",
            parse_mode=ParseMode.HTML,
        )
    finally:
        running_jobs.pop(session.job_id, None)


# ---------------------------------------------------------------------------
# Delete engine
# ---------------------------------------------------------------------------
async def delete_chunk(client: Client, chat_id: int, ids: List[int]) -> Tuple[int, List[int]]:
    """Delete up to 100 messages, then verify. Anything that survived is retried once.

    Returns (messages deleted, ids that still exist)."""
    deleted = 0
    pending = list(ids)
    for _ in range(2):
        result = await with_retry(lambda: client.delete_messages(chat_id, pending))
        if isinstance(result, int) and not isinstance(result, bool):
            deleted += result
        fetched = await with_retry(lambda: client.get_messages(chat_id, pending))
        if not isinstance(fetched, list):
            fetched = [fetched]
        pending = [m.id for m in fetched if m is not None and not m.empty]
        if not pending:
            break
    return deleted, pending


async def run_delete_job(client: Client, admin_id: int, session: Session, status: Message) -> None:
    started = time.monotonic()
    ids = list(range(session.start_id, session.end_id + 1))
    total = len(ids)
    deleted = 0
    remaining: List[int] = []
    processed = 0
    last_edit = 0.0

    try:
        await client.resolve_peer(session.source_id)  # fail fast if the channel is not accessible

        for offset in range(0, total, BATCH_SIZE):
            if session.cancel:
                break
            chunk_ids = ids[offset: offset + BATCH_SIZE]
            count, left = await delete_chunk(client, session.source_id, chunk_ids)
            deleted += count
            remaining.extend(left)
            processed += len(chunk_ids)

            if time.monotonic() - last_edit >= PROGRESS_INTERVAL:
                last_edit = time.monotonic()
                await safe_edit(
                    status,
                    f"🗑 <b>Deleting in progress</b>\n\n"
                    f"Processed: <code>{processed}/{total}</code>\n"
                    f"Deleted: <code>{deleted}</code>",
                    parse_mode=ParseMode.HTML,
                )

        elapsed = int(time.monotonic() - started)
        report = [
            "🛑 <b>Deletion stopped</b>" if session.cancel else "✅ <b>Deletion completed</b>",
            "",
            f"Channel: <b>{html.escape(session.source_title)}</b>",
            f"Range: <code>{session.start_id} → {session.end_id}</code>",
            f"Deleted: <code>{deleted}</code>",
            f"Time taken: <code>{elapsed}s</code>",
        ]
        if remaining:
            report.append(f"\n⚠️ Could not delete these IDs:\n<code>{format_ids(remaining)}</code>")
        await safe_edit(status, "\n".join(report), parse_mode=ParseMode.HTML)

    except Exception as exc:  # noqa: BLE001 - surface any failure to the admin
        logger.exception("Delete job failed")
        await safe_edit(
            status,
            f"❌ <b>Deletion failed</b>\n\n<code>{html.escape(str(exc))}</code>\n\n"
            "Make sure the bot is an admin of that channel with the "
            "<b>Delete messages</b> permission.",
            parse_mode=ParseMode.HTML,
        )
    finally:
        running_jobs.pop(session.job_id, None)


# ---------------------------------------------------------------------------
# Index engine (no forwarding)
# ---------------------------------------------------------------------------
async def run_index_job(client: Client, admin_id: int, session: Session, status: Message) -> None:
    started = time.monotonic()
    ids = list(range(session.start_id, session.end_id + 1))
    total = len(ids)
    entries: List[IndexEntry] = []
    scanned = 0
    skipped = 0
    current_key: SectionKey = ("package", DEFAULT_PACKAGE, None)
    last_edit = 0.0

    try:
        await client.resolve_peer(session.source_id)
        await client.resolve_peer(session.target_id)
        source_chat = await client.get_chat(session.source_id)  # index links point here

        for offset in range(0, total, BATCH_SIZE):
            if session.cancel:
                break
            chunk_ids = ids[offset: offset + BATCH_SIZE]
            fetched = await with_retry(lambda: client.get_messages(session.source_id, chunk_ids))
            if not isinstance(fetched, list):
                fetched = [fetched]

            for msg in fetched:
                if msg is None or msg.empty or msg.service:
                    skipped += 1
                else:
                    current_key = update_entries(entries, current_key, msg, msg.id)

            scanned += len(chunk_ids)
            if time.monotonic() - last_edit >= PROGRESS_INTERVAL:
                last_edit = time.monotonic()
                await safe_edit(
                    status,
                    f"⏳ <b>Reading messages</b>\n\n"
                    f"Processed: <code>{scanned}/{total}</code>\n"
                    f"Index entries: <code>{len(entries)}</code>",
                    parse_mode=ParseMode.HTML,
                )

        index_posted = False
        if not session.cancel and entries:
            await safe_edit(status, "🗂 Building the index…")
            await post_index_pages(
                client, session.target_id, build_index_pages(entries, source_chat)
            )
            index_posted = True

        elapsed = int(time.monotonic() - started)
        report = [
            "🛑 <b>Indexing stopped</b>" if session.cancel else "✅ <b>Indexing completed</b>",
            "",
            f"Channel: <b>{html.escape(session.source_title)}</b>",
            f"Range: <code>{session.start_id} → {session.end_id}</code>",
            f"Index entries: <code>{len(entries)}</code> "
            f"({'posted' if index_posted else 'not posted'})",
            f"Time taken: <code>{elapsed}s</code>",
        ]
        if not entries and not session.cancel:
            report.append("\n⚠️ No messages with a recognised index format were found in this range.")
        await safe_edit(status, "\n".join(report), parse_mode=ParseMode.HTML)

    except Exception as exc:  # noqa: BLE001 - surface any failure to the admin
        logger.exception("Index job failed")
        await safe_edit(
            status,
            f"❌ <b>Indexing failed</b>\n\n<code>{html.escape(str(exc))}</code>\n\n"
            "Make sure the bot is an admin of the channel(s).",
            parse_mode=ParseMode.HTML,
        )
    finally:
        running_jobs.pop(session.job_id, None)


# ---------------------------------------------------------------------------
# Live engine
# ---------------------------------------------------------------------------
def live_panel_markup(task: LiveTask) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("✅ Forward Complete", callback_data=f"live:ask_complete:{task.task_id}")],
        [InlineKeyboardButton("⏹ Stop", callback_data=f"live:ask_stop:{task.task_id}")],
    ])


def live_panel_text(task: LiveTask, note: str = "") -> str:
    return (
        f"🔴 <b>Live forwarding</b> <code>#{task.task_id}</code>\n\n"
        f"Source: <b>{html.escape(task.source_title)}</b>\n"
        f"Target: <b>{html.escape(task.target_title)}</b>\n"
        f"Forwarded: <code>{task.forwarded}</code>\n"
        f"Last source ID handled: <code>{task.next_id - 1}</code>\n"
        f"Index entries: <code>{len(task.entries)}</code>\n\n"
        "New posts are forwarded as they arrive. When the source has finished, "
        "tap <b>Forward Complete</b> to build the index." + note
    )


async def persist_live_task(task: LiveTask) -> None:
    try:
        await live_col.replace_one({"_id": task.task_id}, task.to_doc(), upsert=True)
    except Exception:  # noqa: BLE001 - a database hiccup must not stop forwarding
        logger.exception("Could not save live task state")


async def forget_live_task(task_id: str) -> None:
    paused_docs.pop(task_id, None)
    try:
        await live_col.delete_one({"_id": task_id})
    except Exception:  # noqa: BLE001
        logger.exception("Could not delete live task state")


async def live_step(client: Client, task: LiveTask, source_peer, target_peer) -> bool:
    """Forward every message currently available after task.next_id (up to 100).

    Returns True when progress was made, False when there is nothing new yet."""
    ids = list(range(task.next_id, task.next_id + BATCH_SIZE))
    fetched = await with_retry(lambda: client.get_messages(task.source_id, ids))
    if not isinstance(fetched, list):
        fetched = [fetched]
    present = [m for m in fetched if m is not None and not m.empty]

    if not present:
        if task.latest_seen >= ids[-1]:
            task.next_id = ids[-1] + 1   # a long run of deleted IDs: jump over it
            return True
        return False

    deliverable = [m for m in present if not m.service]
    if deliverable:
        mapping, missing = await forward_batch(
            client, source_peer, target_peer,
            task.source_id, task.target_id,
            [m.id for m in deliverable],
        )
        task.failed.extend(missing)
        for msg in deliverable:
            new_id = mapping.get(msg.id)
            if new_id is None:
                continue
            task.forwarded += 1
            task.current_key = update_entries(task.entries, task.current_key, msg, new_id)

    task.next_id = max(m.id for m in present) + 1
    return True


async def run_live_task(client: Client, task: LiveTask) -> None:
    last_edit = 0.0
    try:
        source_peer = await client.resolve_peer(task.source_id)
        target_peer = await client.resolve_peer(task.target_id)
        target_chat = await client.get_chat(task.target_id)

        while not task.stop:
            task.wake.clear()
            if await live_step(client, task, source_peer, target_peer):
                await persist_live_task(task)
                finishing = task.complete or task.stop
                if not finishing and time.monotonic() - last_edit >= LIVE_PANEL_INTERVAL:
                    last_edit = time.monotonic()
                    await safe_edit(
                        task.status, live_panel_text(task),
                        parse_mode=ParseMode.HTML, reply_markup=live_panel_markup(task),
                    )
                continue
            if task.complete:
                break  # everything available has been forwarded
            try:
                await asyncio.wait_for(task.wake.wait(), LIVE_POLL_SECONDS)
            except asyncio.TimeoutError:
                pass

        index_posted = False
        if not task.stop and task.entries:
            await post_index_pages(
                client, task.target_id, build_index_pages(task.entries, target_chat)
            )
            index_posted = True

        report = [
            "🛑 <b>Live forwarding stopped</b>" if task.stop else "✅ <b>Live forwarding completed</b>",
            "",
            f"Source: <b>{html.escape(task.source_title)}</b>",
            f"Target: <b>{html.escape(task.target_title)}</b>",
            f"Forwarded: <code>{task.forwarded}</code>",
            f"Index entries: <code>{len(task.entries)}</code> "
            f"({'posted' if index_posted else 'not posted'})",
        ]
        if task.failed:
            report.append(f"\n⚠️ Failed IDs:\n<code>{format_ids(task.failed)}</code>")
        await safe_edit(task.status, "\n".join(report), parse_mode=ParseMode.HTML)
        await forget_live_task(task.task_id)

    except Exception as exc:  # noqa: BLE001 - keep the saved state so the task can be resumed
        logger.exception("Live task failed")
        await persist_live_task(task)
        paused_docs[task.task_id] = task.to_doc()
        await safe_edit(
            task.status,
            f"❌ <b>Live forwarding paused</b>\n\n<code>{html.escape(str(exc))}</code>\n\n"
            "Make sure the bot is an admin in both channels, then send /live and tap "
            "<b>Resume</b>. Nothing forwarded so far is lost.",
            parse_mode=ParseMode.HTML,
        )
    finally:
        if live_tasks.get(task.task_id) is task:
            live_tasks.pop(task.task_id, None)


async def start_live_task(client: Client, task: LiveTask, status: Message) -> None:
    task.status = status
    live_tasks[task.task_id] = task
    await persist_live_task(task)
    runner = asyncio.create_task(run_live_task(client, task))
    background_tasks.add(runner)
    runner.add_done_callback(background_tasks.discard)


async def resume_live_tasks(client: Client) -> None:
    """Called once at startup: pick up live tasks that were running before a restart."""
    async for doc in live_col.find():
        task = LiveTask.from_doc(doc)
        try:
            await client.resolve_peer(task.source_id)
            await client.resolve_peer(task.target_id)
            await client.get_chat(task.target_id)
        except Exception as exc:  # noqa: BLE001
            logger.warning("Could not resume live task of %s: %s", task.admin_id, exc)
            paused_docs[task.task_id] = doc
            try:
                await client.send_message(
                    task.admin_id,
                    "♻️ <b>Live forwarding paused</b>\n\n"
                    "The bot restarted and lost access to the channels. Send /live and tap "
                    "<b>Resume</b>; you will only need to forward one message from each channel. "
                    "Nothing forwarded so far is lost.",
                    parse_mode=ParseMode.HTML,
                )
            except RPCError:
                pass
            continue
        try:
            status = await client.send_message(
                task.admin_id,
                live_panel_text(task, "\n\n♻️ Resumed after a bot restart."),
                parse_mode=ParseMode.HTML,
                reply_markup=live_panel_markup(task),
            )
        except RPCError:
            continue
        await start_live_task(client, task, status)


# ---------------------------------------------------------------------------
# TXT engine (/txt_checker and /txt_update)
# ---------------------------------------------------------------------------
# A TXT line looks like:  (Topic) (Subfolder) Title: https://link
TXT_LINE_RE = re.compile(
    r"^((?:\([^()]*(?:\([^()]*\)[^()]*)*\)\s*)*)(.*?):\s*(https?://\S+)\s*$"
)
TXT_GROUP_RE = re.compile(r"\(([^()]*(?:\([^()]*\)[^()]*)*)\)")
EXTENSION_RE = re.compile(r"\.(mp4|mkv|avi|mov|webm|m3u8|pdf|zip)\s*$", re.IGNORECASE)
NEAR_MATCH_THRESHOLD = 0.88
NEAR_MATCH_MAX_COMPARISONS = 400_000
REPORT_LIST_LIMIT = 10

ItemKey = Tuple[str, str]  # (comparable topic, comparable title)


@dataclass
class TxtRow:
    line_no: int
    raw: str                  # the original line, written back unchanged
    key: Optional[ItemKey]    # None when the line does not follow the expected format
    title: str


def match_text(value: str, drop_extension: bool = False) -> str:
    """Comparable form of a name: letters, digits and marks only, lower case,
    single spaces. Emoji, punctuation and file extensions do not matter."""
    value = normalize_line(value).strip()
    if drop_extension:
        value = EXTENSION_RE.sub("", value)
    folded = "".join(ch if unicodedata.category(ch)[0] in "LNM" else " " for ch in value)
    return " ".join(folded.lower().split())


def decode_txt(data: bytes) -> str:
    try:
        return data.decode("utf-8-sig")
    except UnicodeDecodeError:
        return data.decode("utf-8", errors="replace")


def parse_txt(text: str) -> List[TxtRow]:
    rows: List[TxtRow] = []
    for number, line in enumerate(text.splitlines(), start=1):
        if not line.strip():
            continue
        match = TXT_LINE_RE.match(line)
        if not match:
            rows.append(TxtRow(number, line, None, ""))
            continue
        groups = TXT_GROUP_RE.findall(match.group(1))
        topic = groups[0] if groups else ""
        title = match.group(2).strip()
        rows.append(TxtRow(number, line, (match_text(topic), match_text(title, True)), title))
    return rows


def parse_channel_item(text: str) -> Optional[Tuple[str, str]]:
    """Read the Topic and Title lines of a channel caption: returns (topic, title)."""
    title = topic = None
    for line in (text or "").splitlines():
        line = normalize_line(line)
        if title is None and (match := TITLE_RE.match(line)):
            title = clean_value(match.group(1))
        elif topic is None and (match := TOPIC_ONLY_RE.match(line)):
            topic = clean_value(match.group(1))
    return (topic or "", title) if title else None


def split_rows(rows: List[TxtRow], known: Counter) -> Tuple[List[TxtRow], List[TxtRow], Counter]:
    """Split TXT rows into (new, already known, known items never seen in the TXT).

    Duplicates are matched by count: if an item is known once but appears twice
    in the TXT, the first one is treated as known and the second as new."""
    remaining = Counter(known)
    kept: List[TxtRow] = []
    removed: List[TxtRow] = []
    for row in rows:
        if row.key is not None and remaining[row.key] > 0:
            remaining[row.key] -= 1
            removed.append(row)
        else:
            kept.append(row)
    return kept, removed, +remaining  # unary plus drops zero counts


def find_near_matches(
    kept: List[TxtRow], leftover: Counter, labels: Dict[ItemKey, str]
) -> List[Tuple[str, str]]:
    """Pair leftover channel items with kept TXT rows whose names are almost equal.

    Names with different numbers (Lecture 1 / Lecture 11) never count as similar."""
    if len(leftover) * max(len(kept), 1) > NEAR_MATCH_MAX_COMPARISONS:
        return []
    pairs: List[Tuple[str, str]] = []
    for key in leftover:
        topic_key, title_key = key
        matcher = difflib.SequenceMatcher(None, "", title_key)
        digits = re.findall(r"\d+", title_key)
        best: Optional[Tuple[float, TxtRow]] = None
        for row in kept:
            if row.key is None or row.key[0] != topic_key or re.findall(r"\d+", row.key[1]) != digits:
                continue
            matcher.set_seq1(row.key[1])
            if matcher.real_quick_ratio() < NEAR_MATCH_THRESHOLD or matcher.quick_ratio() < NEAR_MATCH_THRESHOLD:
                continue
            ratio = matcher.ratio()
            if ratio >= NEAR_MATCH_THRESHOLD and (best is None or ratio > best[0]):
                best = (ratio, row)
        if best:
            pairs.append((best[1].title, labels[key]))
    return pairs


def shorten(value: str, limit: int = 60) -> str:
    return value if len(value) <= limit else value[: limit - 1] + "…"


def code_list(items: List[str]) -> str:
    shown = "\n".join(f"• <code>{html.escape(shorten(item))}</code>" for item in items[:REPORT_LIST_LIMIT])
    extra = f"\n… and {len(items) - REPORT_LIST_LIMIT} more" if len(items) > REPORT_LIST_LIMIT else ""
    return shown + extra


async def send_txt_result(client: Client, chat_id: int, rows: List[TxtRow], source_name: str) -> None:
    """Send the remaining lines back as a new TXT file."""
    stem = os.path.splitext(os.path.basename(source_name))[0] or "links"
    caption = f"New links only: {len(rows)}"
    with tempfile.TemporaryDirectory() as folder:
        path = os.path.join(folder, "result.txt")
        with open(path, "w", encoding="utf-8") as handle:
            handle.write("\n".join(row.raw for row in rows) + "\n")
        await with_retry(
            lambda: client.send_document(chat_id, path, caption=caption, file_name=f"{stem}_NEW.txt")
        )


async def run_txt_checker(client: Client, admin_id: int, session: Session, status: Message) -> None:
    """Read the titles of the videos/PDFs in a channel range and remove them from the TXT."""
    ids = list(range(session.start_id, session.end_id + 1))
    total = len(ids)
    uploaded: Counter = Counter()
    labels: Dict[ItemKey, str] = {}
    items_read = 0
    without_title = 0
    scanned = 0
    last_edit = 0.0

    try:
        await client.resolve_peer(session.source_id)
        for offset in range(0, total, BATCH_SIZE):
            if session.cancel:
                break
            chunk_ids = ids[offset: offset + BATCH_SIZE]
            fetched = await with_retry(lambda: client.get_messages(session.source_id, chunk_ids))
            if not isinstance(fetched, list):
                fetched = [fetched]
            for msg in fetched:
                if msg is None or msg.empty or msg.service or not (msg.video or msg.document):
                    continue
                parsed = parse_channel_item(msg.caption or "")
                if parsed is None:
                    without_title += 1
                    continue
                topic, title = parsed
                key = (match_text(topic), match_text(title, True))
                uploaded[key] += 1
                labels.setdefault(key, title)
                items_read += 1

            scanned += len(chunk_ids)
            if time.monotonic() - last_edit >= PROGRESS_INTERVAL:
                last_edit = time.monotonic()
                await safe_edit(
                    status,
                    f"⏳ <b>Reading the channel</b>\n\n"
                    f"Processed: <code>{scanned}/{total}</code>\n"
                    f"Items found: <code>{items_read}</code>",
                    parse_mode=ParseMode.HTML,
                )

        if session.cancel:
            await safe_edit(status, "🛑 <b>TXT check stopped</b>", parse_mode=ParseMode.HTML)
            return

        rows = parse_txt(session.txt_text or "")
        kept, removed, leftover = split_rows(rows, uploaded)
        near = find_near_matches(kept, leftover, labels)
        unreadable = sum(1 for row in rows if row.key is None)

        report = [
            "✅ <b>TXT check completed</b>",
            "",
            f"Channel: <b>{html.escape(session.source_title)}</b>",
            f"Range: <code>{session.start_id} → {session.end_id}</code>",
            f"Channel items read: <code>{items_read}</code>",
            f"TXT lines: <code>{len(rows)}</code>",
            f"Already uploaded (removed): <code>{len(removed)}</code>",
            f"New links (kept): <code>{len(kept)}</code>",
        ]
        if unreadable:
            report.append(f"Unreadable TXT lines (kept as new): <code>{unreadable}</code>")
        if without_title:
            report.append(f"Channel items without a Title line: <code>{without_title}</code>")
        if leftover:
            names = [labels[key] for key in leftover]
            report.append(f"\nChannel items not found in the TXT: <code>{sum(leftover.values())}</code>\n{code_list(names)}")
        if near:
            report.append(
                "\n⚠️ Possible matches (kept in the new TXT):\n"
                + code_list([f"{txt_title}  ≈  {channel_title}" for txt_title, channel_title in near])
            )
        if not kept:
            report.append("\nNo new links: everything in the TXT is already uploaded.")
        await safe_edit(status, "\n".join(report), parse_mode=ParseMode.HTML)
        if kept:
            await send_txt_result(client, admin_id, kept, session.txt_name)

    except Exception as exc:  # noqa: BLE001 - surface any failure to the admin
        logger.exception("TXT check failed")
        await safe_edit(
            status,
            f"❌ <b>TXT check failed</b>\n\n<code>{html.escape(str(exc))}</code>\n\n"
            "Make sure the bot is an admin of the channel.",
            parse_mode=ParseMode.HTML,
        )
    finally:
        running_jobs.pop(session.job_id, None)


async def run_txt_update(client: Client, message: Message, session: Session, new_text: str, new_name: str) -> None:
    """Compare an old and a new TXT and send back only the links that are new."""
    old_rows = parse_txt(session.txt_text or "")
    new_rows = parse_txt(new_text)
    known = Counter(row.key for row in old_rows if row.key is not None)
    kept, removed, leftover = split_rows(new_rows, known)
    unreadable = sum(1 for row in new_rows if row.key is None)

    report = [
        "✅ <b>TXT update completed</b>",
        "",
        f"Old TXT lines: <code>{len(old_rows)}</code>",
        f"New TXT lines: <code>{len(new_rows)}</code>",
        f"Already in the old TXT (removed): <code>{len(removed)}</code>",
        f"New links (kept): <code>{len(kept)}</code>",
    ]
    if unreadable:
        report.append(f"Unreadable lines in the new TXT (kept as new): <code>{unreadable}</code>")
    if leftover:
        report.append(f"Old TXT items missing from the new TXT: <code>{sum(leftover.values())}</code>")
    if not kept:
        report.append("\nNo new links: the new TXT has nothing beyond the old one.")
    await message.reply_text("\n".join(report), parse_mode=ParseMode.HTML)
    if kept:
        await send_txt_result(client, message.from_user.id, kept, new_name)


# ---------------------------------------------------------------------------
# Daily schedule engine (/daily_schedule)
# ---------------------------------------------------------------------------
SCHEDULE_TZ = ZoneInfo(SCHEDULE_TIMEZONE)
TZ_LABEL = "IST" if SCHEDULE_TIMEZONE == "Asia/Kolkata" else SCHEDULE_TIMEZONE
CLOCK_RE = re.compile(r"^\s*(\d{1,2})(?:[:.](\d{2}))?\s*([ap]m)?\s*$", re.IGNORECASE)
running_schedules: set = set()  # schedule IDs being posted right now


def parse_clock(text: str) -> Optional[Tuple[int, int]]:
    """Parse "09:00", "9.30", "9 pm" or "9:30 AM" into (hour, minute)."""
    match = CLOCK_RE.match(text or "")
    if not match:
        return None
    hour, minute = int(match.group(1)), int(match.group(2) or 0)
    meridiem = (match.group(3) or "").lower()
    if meridiem:
        if not 1 <= hour <= 12:
            return None
        hour = hour % 12 + (12 if meridiem == "pm" else 0)
    if hour > 23 or minute > 59:
        return None
    return hour, minute


def utcnow() -> datetime:
    """Current UTC time as a naive datetime (the form MongoDB stores)."""
    return datetime.now(timezone.utc).replace(tzinfo=None)


def next_occurrence(hour: int, minute: int, after: datetime) -> datetime:
    """The next time the local clock shows hour:minute after the given UTC moment."""
    local_after = after.replace(tzinfo=timezone.utc).astimezone(SCHEDULE_TZ)
    candidate = local_after.replace(hour=hour, minute=minute, second=0, microsecond=0)
    if candidate <= local_after:
        candidate += timedelta(days=1)
    return candidate.astimezone(timezone.utc).replace(tzinfo=None)


def format_local(moment: Optional[datetime]) -> str:
    if moment is None:
        return "-"
    local = moment.replace(tzinfo=timezone.utc).astimezone(SCHEDULE_TZ)
    return local.strftime("%d %b, %I:%M %p") + f" {TZ_LABEL}"


def describe_source(message: Message) -> str:
    """A short label for the scheduled message, shown in lists."""
    snippet = clean_value(message.text or message.caption or "")[:40]
    if message.video:
        kind = "🎬 Video"
    elif message.document:
        kind = "📄 " + (getattr(message.document, "file_name", None) or "Document")
    elif message.photo:
        kind = "🖼 Photo"
    else:
        kind = ""
    return (f"{kind} {snippet}".strip() or "Message")[:50]


async def owner_channels(owner: int) -> List[dict]:
    items = await channels_col.find({"owner": owner}).to_list(None)
    return sorted(items, key=lambda item: item["title"].lower())


async def owner_schedules(owner: int) -> List[dict]:
    items = await schedules_col.find({"owner": owner}).to_list(None)
    return sorted(items, key=lambda item: (item["hour"], item["minute"], item["_id"]))


async def get_schedule(schedule_id: str, owner: int) -> Optional[dict]:
    doc = await schedules_col.find_one({"_id": schedule_id})
    return doc if doc and doc["owner"] == owner else None


async def post_to_channel(client: Client, doc: dict, channel_id: int) -> int:
    """Delete the previous post in a channel (if any) and post the message again."""
    old_id = doc.get("posted", {}).get(str(channel_id))
    if old_id:
        try:
            await with_retry(lambda: client.delete_messages(channel_id, old_id))
        except RPCError as exc:  # already deleted by hand, or no permission
            logger.warning("Could not delete the old post in %s: %s", channel_id, exc)
    sent = await with_retry(
        lambda: client.copy_message(
            channel_id, doc["source_chat"], doc["source_msg_id"],
            disable_notification=bool(doc.get("silent")),
        )
    )
    return sent.id


async def execute_schedule(client: Client, doc: dict) -> Tuple[Dict[str, int], List[Tuple[int, str]]]:
    """Run one schedule: every channel gets a fresh post. Returns (new posts, failures)."""
    posted: Dict[str, int] = {}
    failures: List[Tuple[int, str]] = []
    gate = asyncio.Semaphore(SCHEDULE_CONCURRENCY)

    async def one(channel_id: int) -> None:
        async with gate:
            try:
                posted[str(channel_id)] = await post_to_channel(client, doc, channel_id)
            except Exception as exc:  # noqa: BLE001 - one channel must not stop the others
                logger.warning("Schedule %s failed in %s: %s", doc["_id"], channel_id, exc)
                failures.append((channel_id, type(exc).__name__))

    await asyncio.gather(*(one(channel_id) for channel_id in doc["channel_ids"]))
    return posted, failures


async def remove_posts(client: Client, doc: dict) -> int:
    """Delete the posts a schedule currently has in its channels."""
    removed = 0
    for channel_id, message_id in doc.get("posted", {}).items():
        try:
            await with_retry(lambda: client.delete_messages(int(channel_id), message_id))
            removed += 1
        except RPCError as exc:
            logger.warning("Could not remove the post in %s: %s", channel_id, exc)
    return removed


async def run_scheduled_post(client: Client, schedule_id: str, manual: bool = False) -> bool:
    """Post a schedule now. Scheduled runs also move next_run to the next day."""
    if schedule_id in running_schedules:
        return False
    running_schedules.add(schedule_id)
    try:
        doc = await schedules_col.find_one({"_id": schedule_id})
        if not doc or (not manual and not doc["active"]):
            return False
        posted, failures = await execute_schedule(client, doc)
        update = {
            "posted": posted,
            "last_run": utcnow(),
            "last_ok": len(posted),
            "last_total": len(doc["channel_ids"]),
        }
        if not manual:
            update["next_run"] = next_occurrence(doc["hour"], doc["minute"], utcnow())
        await schedules_col.update_one({"_id": schedule_id}, {"$set": update})

        if failures:
            titles = {c["chat_id"]: c["title"] for c in await owner_channels(doc["owner"])}
            lines = [f"• {html.escape(titles.get(cid, str(cid)))}: <code>{reason}</code>" for cid, reason in failures]
            hint = ""
            if len(failures) == len(doc["channel_ids"]):
                hint = "\n\nIf every channel fails, the scheduled message may have been deleted from your chat with the bot."
            try:
                await client.send_message(
                    doc["owner"],
                    f"⚠️ <b>Schedule <code>#{schedule_id}</code></b> posted to "
                    f"{len(posted)}/{len(doc['channel_ids'])} channels.\n\nFailed:\n" + "\n".join(lines) + hint,
                    parse_mode=ParseMode.HTML,
                )
            except RPCError:
                pass
        return True
    except Exception:  # noqa: BLE001
        logger.exception("Scheduled post %s failed", schedule_id)
        return False
    finally:
        running_schedules.discard(schedule_id)


async def scheduler_tick(client: Client) -> None:
    """Start every active schedule whose time has come (also catches up after a restart)."""
    async for doc in schedules_col.find({"active": True, "next_run": {"$lte": utcnow()}}):
        if doc["_id"] in running_schedules:
            continue
        task = asyncio.create_task(run_scheduled_post(client, doc["_id"]))
        background_tasks.add(task)
        task.add_done_callback(background_tasks.discard)


async def scheduler_loop(client: Client) -> None:
    while True:
        try:
            await scheduler_tick(client)
        except Exception:  # noqa: BLE001 - the loop must survive any failure
            logger.exception("Scheduler tick failed")
        await asyncio.sleep(SCHEDULER_TICK_SECONDS)


# ----- screens (shared look: heading, divider, status badges, a Back button everywhere) ------
DIVIDER = "━━━━━━━━━━━━━━━━━━"
Reply = Callable[[str, Optional[InlineKeyboardMarkup]], Awaitable]
quick_sends: Dict[str, dict] = {}  # recent quick sends, kept so they can be undone


def heading(icon: str, name: str, note: str = "") -> str:
    text = f"<b>{icon}  {name}</b>" + (f"  <code>{note}</code>" if note else "")
    return f"{text}\n{DIVIDER}"


def btn(text: str, data: str) -> InlineKeyboardButton:
    return InlineKeyboardButton(text, callback_data=data)


def reply_via(message: Message) -> Reply:
    """Answer with a new message."""
    async def send(text: str, markup: Optional[InlineKeyboardMarkup] = None):
        return await message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=markup)
    return send


def edit_via(message: Message) -> Reply:
    """Answer by editing an existing message."""
    async def send(text: str, markup: Optional[InlineKeyboardMarkup] = None):
        await safe_edit(message, text, parse_mode=ParseMode.HTML, reply_markup=markup)
    return send


def names_of(channel_ids, titles: Dict[int, str], limit: int = 10) -> str:
    names = [html.escape(titles.get(cid, str(cid))) for cid in channel_ids]
    return ", ".join(names[:limit]) + (f" … +{len(names) - limit}" if len(names) > limit else "")


async def menu_screen(owner: int) -> Tuple[str, InlineKeyboardMarkup]:
    channels = await owner_channels(owner)
    schedules = await owner_schedules(owner)
    active = [item for item in schedules if item["active"]]
    upcoming = min((item["next_run"] for item in active), default=None)
    text = (
        heading("📅", "SCHEDULE HUB") + "\n"
        f"📡  Channels        <code>{len(channels)}</code>\n"
        f"🗓  Schedules       <code>{len(schedules)}</code>  ({len(active)} active)\n"
        f"⏭  Next post       <code>{format_local(upcoming)}</code>\n"
        f"{DIVIDER}\n"
        "<i>Daily schedules delete the previous post and publish the message again every "
        "24 hours. Quick send publishes once, right now.</i>"
    )
    return text, InlineKeyboardMarkup([
        [btn("📡 Channels", "ds:channels"), btn("➕ New schedule", "ds:new")],
        [btn("📋 Scheduled messages", "ds:list")],
        [btn("⚡ Quick send", "ds:quick")],
    ])


async def channels_screen(owner: int) -> Tuple[str, InlineKeyboardMarkup]:
    channels = await owner_channels(owner)
    lines = [heading("📡", "YOUR CHANNELS", str(len(channels)))]
    lines += [f"•  {html.escape(c['title'])}" for c in channels] or ["<i>No channels yet.</i>"]
    rows = [[btn("➕ Add channel", "ds:addch")]]
    rows += [[btn(f"🗑 Remove · {c['title'][:28]}", f"ds:rmch:{c['chat_id']}")] for c in channels]
    rows.append([btn("⬅ Back", "ds:menu")])
    return "\n".join(lines), InlineKeyboardMarkup(rows)


async def list_screen(owner: int) -> Tuple[str, InlineKeyboardMarkup]:
    schedules = await owner_schedules(owner)
    lines = [heading("📋", "SCHEDULED MESSAGES", str(len(schedules)))]
    rows = []
    for number, item in enumerate(schedules, start=1):
        state = "✅" if item["active"] else "⏸"
        lines.append(
            f"<b>{number}.</b> {state} <code>{item['hour']:02d}:{item['minute']:02d}</code> · "
            f"{len(item['channel_ids'])} channel{'s' if len(item['channel_ids']) != 1 else ''}\n"
            f"      <i>{html.escape(item['preview'])}</i>"
        )
        rows.append([btn(f"{number} ▸ {item['hour']:02d}:{item['minute']:02d} · {item['preview'][:24]}", f"ds:view:{item['_id']}")])
    if not schedules:
        lines.append("<i>No scheduled messages yet.</i>")
    else:
        lines.append(f"{DIVIDER}\n<i>Tap a message to view, edit, re-time, stop or delete it.</i>")
    rows.append([btn("➕ New schedule", "ds:new"), btn("⚡ Quick send", "ds:quick")])
    rows.append([btn("⬅ Back", "ds:menu")])
    return "\n".join(lines), InlineKeyboardMarkup(rows)


async def detail_screen(owner: int, schedule_id: str) -> Tuple[str, InlineKeyboardMarkup]:
    doc = await get_schedule(schedule_id, owner)
    if not doc:
        return "This schedule no longer exists.", InlineKeyboardMarkup([[btn("⬅ Back", "ds:list")]])
    titles = {c["chat_id"]: c["title"] for c in await owner_channels(owner)}
    last = "-"
    if doc.get("last_run"):
        last = f"{format_local(doc['last_run'])} · {doc.get('last_ok', 0)}/{doc.get('last_total', 0)} posted"
    text = (
        heading("🗓", "SCHEDULE", f"#{doc['_id']}") + "\n"
        f"✉️  Message     <i>{html.escape(doc['preview'])}</i>\n"
        f"🕒  Time          <code>{doc['hour']:02d}:{doc['minute']:02d}</code> {TZ_LABEL}, every day\n"
        f"📡  Channels   ({len(doc['channel_ids'])}) {names_of(doc['channel_ids'], titles)}\n"
        f"🔔  Alerts        {'🔕 silent' if doc.get('silent') else '🔔 on'}\n"
        f"📌  Status        {'✅ Active' if doc['active'] else '⏸ Stopped'}\n"
        f"⏭  Next run     {format_local(doc['next_run']) if doc['active'] else '-'}\n"
        f"✔️  Last run      {last}"
    )
    toggle = btn("⏸ Stop", f"ds:stop:{schedule_id}") if doc["active"] else btn("▶ Resume", f"ds:resume:{schedule_id}")
    return text, InlineKeyboardMarkup([
        [btn("👁 View message", f"ds:viewmsg:{schedule_id}"), btn("✏️ Edit message", f"ds:edit:{schedule_id}")],
        [btn("🕒 Change time", f"ds:time:{schedule_id}"), btn("📡 Channels", f"ds:chs:{schedule_id}")],
        [btn("🚀 Post now", f"ds:now:{schedule_id}"), toggle],
        [btn("🗑 Delete schedule", f"ds:del:{schedule_id}")],
        [btn("⬅ Back", "ds:list")],
    ])


def selection_markup(
    channels: List[dict], selected: set, done_label: str,
    prefix: str = "ds", cancel_label: str = "✖ Cancel", cancel_data: str = "ds:cancel",
) -> InlineKeyboardMarkup:
    rows = [
        [btn(("✅ " if c["chat_id"] in selected else "⬜ ") + c["title"][:30], f"{prefix}:tg:{c['chat_id']}")]
        for c in channels
    ]
    rows.append([btn("☑ Select all" if len(selected) < len(channels) else "⬜ Clear all", f"{prefix}:all")])
    rows.append([btn(done_label, f"{prefix}:seldone"), btn(cancel_label, cancel_data)])
    return InlineKeyboardMarkup(rows)


def confirm_screen(data: dict, channel_titles: List[str]) -> Tuple[str, InlineKeyboardMarkup]:
    shown = ", ".join(html.escape(t) for t in channel_titles[:10]) + (
        f" … +{len(channel_titles) - 10}" if len(channel_titles) > 10 else "")
    text = (
        heading("📋", "CONFIRM SCHEDULE") + "\n"
        f"✉️  Message     <i>{html.escape(data['preview'])}</i>\n"
        f"📡  Channels   ({len(channel_titles)}) {shown}\n"
        f"🕒  Time          <code>{data['hour']:02d}:{data['minute']:02d}</code> {TZ_LABEL}, every day\n"
        f"🔔  Alerts        {'🔕 silent' if data.get('silent') else '🔔 on'}"
    )
    return text, InlineKeyboardMarkup([
        [btn("🔔 Switch to normal" if data.get("silent") else "🔕 Switch to silent", "ds:silent")],
        [btn("✅ Create", "ds:create"), btn("🚀 Create & post now", "ds:createnow")],
        [btn("✖ Cancel", "ds:cancel")],
    ])


def quick_confirm_screen(data: dict, channels: List[dict]) -> Tuple[str, InlineKeyboardMarkup]:
    titles = {c["chat_id"]: c["title"] for c in channels}
    selected = sorted(data["selected"])
    everyone = len(selected) == len(channels)
    text = (
        heading("⚡", "QUICK SEND") + "\n"
        f"✉️  Message     <i>{html.escape(data['preview'])}</i>\n"
        f"📡  Channels   {'all ' if everyone else ''}({len(selected)}/{len(channels)}) {names_of(selected, titles)}\n"
        f"🔔  Alerts        {'🔕 silent' if data.get('silent') else '🔔 on'}\n"
        f"{DIVIDER}\n"
        "<i>The message is published once, right now. Nothing is scheduled.</i>"
    )
    send_label = f"🚀 Send to {'all ' if everyone else ''}{len(selected)} channel{'s' if len(selected) != 1 else ''}"
    return text, InlineKeyboardMarkup([
        [btn(send_label, "qs:send")],
        [btn("📡 Choose channels", "qs:choose"), btn("✏️ Edit message", "qs:edit")],
        [btn("🔔 Switch to normal" if data.get("silent") else "🔕 Switch to silent", "qs:silent")],
        [btn("✖ Cancel", "qs:cancel")],
    ])


ADD_CHANNEL_PROMPT = (
    heading("📡", "ADD CHANNELS") + "\n"
    "Forward <b>one message from each channel</b> you want to post in. The bot must be an "
    "admin there with the <b>Post</b> and <b>Delete messages</b> permissions.\n\n"
    "<i>You can add more channels at any time with /add_channel.</i>\n"
    "Tap <b>Done</b> when you have added them all."
)
QUICK_PROMPT = (
    heading("⚡", "QUICK SEND") + "\n"
    "Send the message you want to publish <b>right now</b> to your channels "
    "(text, photo, video, PDF, anything)."
)


async def add_channel_from_forward(client: Client, message: Message) -> str:
    """Register the channel a forwarded message came from. Returns the reply text."""
    origin = get_forward_origin(message)
    if origin is None:
        return "Please forward a message directly from the channel."
    chat, _ = origin
    title = getattr(chat, "title", None) or str(chat.id)
    try:
        member = await client.get_chat_member(chat.id, "me")
    except RPCError:
        return f"⚠️ The bot is not a member of <b>{html.escape(title)}</b>. Add it as an admin and forward again."
    privileges = getattr(member, "privileges", None)
    if privileges is None:
        return f"⚠️ The bot is not an admin in <b>{html.escape(title)}</b>. Make it an admin and forward again."
    if getattr(privileges, "can_post_messages", None) is False:
        return f"⚠️ The bot cannot post in <b>{html.escape(title)}</b>. Give it the <b>Post messages</b> permission."

    owner = message.from_user.id
    await channels_col.replace_one(
        {"_id": f"{owner}_{chat.id}"},
        {"_id": f"{owner}_{chat.id}", "owner": owner, "chat_id": chat.id,
         "title": title, "username": getattr(chat, "username", None)},
        upsert=True,
    )
    reply = f"✅ Added: <b>{html.escape(title)}</b>"
    if getattr(privileges, "can_delete_messages", None) is False:
        reply += "\n⚠️ The bot cannot delete messages there, so old posts will not be removed. Give it the <b>Delete messages</b> permission."
    return reply + "\n\nForward another channel, or tap Done."


# ----- entry points shared by commands, buttons and the /start menu -----------------------
async def open_hub(user_id: int, reply: Reply) -> None:
    sessions.pop(user_id, None)
    if not await owner_channels(user_id):  # first step: collect the channels
        await open_add_channel(user_id, reply)
        return
    await reply(*await menu_screen(user_id))


async def open_add_channel(user_id: int, reply: Reply) -> None:
    sessions[user_id] = Session(mode=MODE_DAILY, step=STEP_DS_CHANNEL)
    await reply(ADD_CHANNEL_PROMPT, InlineKeyboardMarkup([[btn("✅ Done", "ds:addch_done")]]))


async def open_quick(user_id: int, reply: Reply) -> None:
    channels = await owner_channels(user_id)
    if not channels:
        sessions.pop(user_id, None)
        await reply(
            heading("⚡", "QUICK SEND") + "\nQuick send uses the channels you added for scheduling, "
            "and there are none yet.",
            InlineKeyboardMarkup([[btn("➕ Add channels", "ds:addch")]]),
        )
        return
    sessions[user_id] = Session(
        mode=MODE_DAILY, step=STEP_QS_MESSAGE,
        ds={"quick": True, "selected": {c["chat_id"] for c in channels}, "silent": False},
    )
    await reply(QUICK_PROMPT, InlineKeyboardMarkup([[btn("✖ Cancel", "qs:cancel")]]))


async def open_schedules(user_id: int, reply: Reply) -> None:
    sessions.pop(user_id, None)
    await reply(*await list_screen(user_id))


async def copy_to_channels(
    client: Client, channel_ids: List[int], source_chat: int, source_msg_id: int, silent: bool
) -> Tuple[Dict[str, int], List[Tuple[int, str]]]:
    """Publish a message in several channels at once (no deletion, no schedule)."""
    posted: Dict[str, int] = {}
    failures: List[Tuple[int, str]] = []
    gate = asyncio.Semaphore(SCHEDULE_CONCURRENCY)

    async def one(channel_id: int) -> None:
        async with gate:
            try:
                sent = await with_retry(
                    lambda: client.copy_message(channel_id, source_chat, source_msg_id, disable_notification=silent)
                )
                posted[str(channel_id)] = sent.id
            except Exception as exc:  # noqa: BLE001 - one channel must not stop the others
                logger.warning("Quick send failed in %s: %s", channel_id, exc)
                failures.append((channel_id, type(exc).__name__))

    await asyncio.gather(*(one(channel_id) for channel_id in channel_ids))
    return posted, failures


async def handle_daily_input(client: Client, message: Message, session: Session) -> None:
    """Messages sent while a schedule or quick-send step is waiting for them."""
    user_id = message.from_user.id
    data = session.ds

    if session.step == STEP_DS_CHANNEL:
        reply = await add_channel_from_forward(client, message)
        await message.reply_text(
            reply, parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([[btn("✅ Done", "ds:addch_done")]]),
        )

    elif session.step in (STEP_DS_MESSAGE, STEP_DS_EDIT, STEP_QS_MESSAGE, STEP_QS_EDIT):
        if message.media_group_id:
            await message.reply_text("Albums are not supported. Please send a single message.")
            return
        preview = describe_source(message)
        if session.step == STEP_DS_MESSAGE:
            data.update(source_chat=message.chat.id, source_msg_id=message.id, preview=preview)
            session.step = STEP_DS_SELECT
            channels = await owner_channels(user_id)
            await message.reply_text(
                heading("📡", "CHOOSE CHANNELS") + "\n✅ Message saved. <b>Do not delete it from this chat</b> "
                "while the schedule is running.\n\nSelect the channels that should get it:",
                parse_mode=ParseMode.HTML,
                reply_markup=selection_markup(channels, data["selected"], "Next ➜"),
            )
        elif session.step == STEP_DS_EDIT:
            data.update(new_chat=message.chat.id, new_msg_id=message.id, new_preview=preview)
            session.step = STEP_DS_EDIT_CHOICE
            await message.reply_text(
                heading("✏️", "EDIT MESSAGE", f"#{data['schedule_id']}") + f"\n✅ New message received:\n<i>{html.escape(preview)}</i>\n\n"
                "When should it go live?",
                parse_mode=ParseMode.HTML,
                reply_markup=InlineKeyboardMarkup([
                    [btn("⏭ From the next run", "ds:editnext")],
                    [btn("⚡ Update the channels now", "ds:editnow")],
                    [btn("✖ Cancel", f"ds:view:{data['schedule_id']}")],
                ]),
            )
        else:  # quick send: first message, or a replacement from "Edit message"
            data.update(source_chat=message.chat.id, source_msg_id=message.id, preview=preview)
            session.step = STEP_QS_CONFIRM
            text, markup = quick_confirm_screen(data, await owner_channels(user_id))
            await message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=markup)

    elif session.step == STEP_DS_TIME:
        clock = parse_clock(message.text or "")
        if clock is None:
            await message.reply_text(
                "I could not read that time. Send it like <code>09:00</code> or <code>9:30 pm</code>.",
                parse_mode=ParseMode.HTML,
            )
            return
        data["hour"], data["minute"] = clock
        if data.get("retime"):  # changing the time of an existing schedule
            schedule_id = data["schedule_id"]
            doc = await get_schedule(schedule_id, user_id)
            sessions.pop(user_id, None)
            if not doc:
                await message.reply_text("This schedule no longer exists.")
                return
            update = {"hour": clock[0], "minute": clock[1]}
            if doc["active"]:
                update["next_run"] = next_occurrence(clock[0], clock[1], utcnow())
            await schedules_col.update_one({"_id": schedule_id}, {"$set": update})
            await message.reply_text("✅ Time updated.")
            text, markup = await detail_screen(user_id, schedule_id)
            await message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=markup)
            return
        session.step = STEP_DS_CONFIRM
        titles = {c["chat_id"]: c["title"] for c in await owner_channels(user_id)}
        text, markup = confirm_screen(data, [titles.get(cid, str(cid)) for cid in sorted(data["selected"])])
        await message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=markup)

    else:
        await message.reply_text("Please use the buttons above, or send /stop to cancel.")


# ---------------------------------------------------------------------------
# Commands
# ---------------------------------------------------------------------------
START_TEXT = (
    "🤖  <b>BULK FORWARD BOT</b>\n"
    f"{DIVIDER}\n"
    "<i>Fast, order-safe forwarding for channel batches, with a built-in scheduler.</i>\n\n"
    "📦  <b>FORWARD &amp; BATCH TOOLS</b>\n"
    "/forward  ·  Copy a message range to another channel, with an index\n"
    "/mixforward  ·  Forward a mixed-up range in number order\n"
    "/live  ·  Forward new posts as they arrive, then build the index\n"
    "/index  ·  Build an index for an existing batch\n"
    "/delete  ·  Delete a range of messages from a channel\n"
    "/txt_checker  ·  Remove already-uploaded items from a TXT of links\n"
    "/txt_update  ·  Get only the new links from an old and a new TXT\n"
    "/tasks  ·  See your running tasks\n"
    "/stop  ·  Stop a running task\n\n"
    "📅  <b>SCHEDULE TOOLS</b>\n"
    "/add_channel  ·  Add channels (once; add more any time)\n"
    "/daily_schedule  ·  Daily posts: delete and repost every 24 hours\n"
    "/quick_schedule  ·  Send a message to all your channels right now\n"
    "/schedules  ·  View, edit, re-time or delete scheduled messages"
)
OWNER_TEXT = (
    "\n\n⚙️  <b>ADMIN</b>  <i>(owner only)</i>\n"
    "/add  ·  Add an admin\n"
    "/remove  ·  Remove an admin\n"
    "/admins  ·  List all admins"
)
START_MARKUP = InlineKeyboardMarkup([
    [InlineKeyboardButton("📅 Schedule Hub", callback_data="home:daily"),
     InlineKeyboardButton("⚡ Quick Send", callback_data="home:quick")],
    [InlineKeyboardButton("📡 Add Channel", callback_data="home:addch"),
     InlineKeyboardButton("📋 Scheduled Messages", callback_data="home:list")],
])


async def deny_access(message: Message) -> None:
    await message.reply_text(
        "⛔ Access restricted. Contact the owner to be added as an admin.\n"
        f"Your user ID: <code>{message.from_user.id}</code>",
        parse_mode=ParseMode.HTML,
    )


async def begin_session(message: Message, mode: str) -> bool:
    """Common entry point for /forward, /index, /delete and /live."""
    user_id = message.from_user.id
    if not await is_admin(user_id):
        await deny_access(message)
        return False
    if count_admin_tasks(user_id) >= MAX_TASKS_PER_ADMIN:
        await message.reply_text(
            f"You already have {MAX_TASKS_PER_ADMIN} tasks running. "
            "Use /tasks to see them, or /stop to end one."
        )
        return False
    sessions[user_id] = Session(mode=mode)
    return True


@app.on_message(filters.command("start") & filters.private)
async def start_command(client: Client, message: Message):
    user_id = message.from_user.id
    if not await is_admin(user_id):
        await deny_access(message)
        return
    text = START_TEXT + (OWNER_TEXT if user_id == OWNER_ID else "")
    await message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=START_MARKUP)


@app.on_message(filters.command("forward") & filters.private)
async def forward_command(client: Client, message: Message):
    if not await begin_session(message, MODE_FORWARD):
        return
    await message.reply_text(
        "📨 <b>Bulk Forward</b>\n\n"
        "<b>Step 1/3:</b> Forward the <b>first message</b> of the range "
        "from the <b>source channel</b>.",
        parse_mode=ParseMode.HTML,
    )


@app.on_message(filters.command("mixforward") & filters.private)
async def mixforward_command(client: Client, message: Message):
    if not await begin_session(message, MODE_MIX):
        return
    await message.reply_text(
        "🔀 <b>Mix Forward</b>\n\n"
        "Forwards a range in the order of the number each caption starts with, "
        "even if the source channel is mixed up.\n\n"
        "<b>Step 1/3:</b> Forward the <b>first message</b> of the range "
        "from the <b>source channel</b>.",
        parse_mode=ParseMode.HTML,
    )


@app.on_message(filters.command("live") & filters.private)
async def live_command(client: Client, message: Message):
    user_id = message.from_user.id
    if not await is_admin(user_id):
        await deny_access(message)
        return

    saved = [d for d in paused_docs.values() if d.get("admin_id", d["_id"]) == user_id]
    if saved:  # offer to resume tasks that were interrupted by a restart
        lines = ["♻️ <b>Saved live tasks</b>\n"]
        rows = []
        for doc in saved:
            lines.append(
                f"• <code>#{doc['_id']}</code> {html.escape(doc['source_title'])} → "
                f"{html.escape(doc['target_title'])} (forwarded {doc.get('forwarded', 0)})"
            )
            rows.append([
                InlineKeyboardButton(f"▶ Resume #{doc['_id']}", callback_data=f"live:resume:{doc['_id']}"),
                InlineKeyboardButton("🗑 Discard", callback_data=f"live:discard:{doc['_id']}"),
            ])
        rows.append([InlineKeyboardButton("🆕 Start new live task", callback_data="live:new")])
        await message.reply_text(
            "\n".join(lines), parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(rows)
        )
        return

    if not await begin_session(message, MODE_LIVE):
        return
    await message.reply_text(LIVE_STEP_1, parse_mode=ParseMode.HTML)


LIVE_STEP_1 = (
    "🔴 <b>Live Forward</b>\n\n"
    "<b>Step 1/2:</b> Forward the message of the <b>source channel</b> to start from. "
    "That message and everything posted after it will be forwarded as it arrives."
)


async def schedule_entry(message: Message, opener) -> None:
    """Admin check shared by the schedule commands."""
    user_id = message.from_user.id
    if not await is_admin(user_id):
        await deny_access(message)
        return
    await opener(user_id, reply_via(message))


@app.on_message(filters.command("daily_schedule") & filters.private)
async def daily_schedule_command(client: Client, message: Message):
    await schedule_entry(message, open_hub)


@app.on_message(filters.command("add_channel") & filters.private)
async def add_channel_command(client: Client, message: Message):
    await schedule_entry(message, open_add_channel)


@app.on_message(filters.command("quick_schedule") & filters.private)
async def quick_schedule_command(client: Client, message: Message):
    await schedule_entry(message, open_quick)


@app.on_message(filters.command("schedules") & filters.private)
async def schedules_command(client: Client, message: Message):
    await schedule_entry(message, open_schedules)


@app.on_message(filters.command("txt_checker") & filters.private)
async def txt_checker_command(client: Client, message: Message):
    if not await begin_session(message, MODE_TXTCHECK):
        return
    await message.reply_text(
        "📄 <b>TXT Checker</b>\n\n"
        "Reads the videos and PDFs already uploaded in a channel and removes them "
        "from a TXT of links, so only the new links remain.\n\n"
        "<b>Step 1/3:</b> Forward the <b>first message</b> of the batch from the channel.\n\n"
        "<i>The bot must be an admin of that channel.</i>",
        parse_mode=ParseMode.HTML,
    )


@app.on_message(filters.command(["txt_update", "txt_updet"]) & filters.private)
async def txt_update_command(client: Client, message: Message):
    if not await begin_session(message, MODE_TXTUPDATE):
        return
    sessions[message.from_user.id].step = STEP_AWAIT_OLD_TXT
    await message.reply_text(
        "📄 <b>TXT Update</b>\n\n"
        "Compares an old TXT with a new one and gives you a TXT with only the new links.\n\n"
        "<b>Step 1/2:</b> Send the <b>old TXT</b> file.",
        parse_mode=ParseMode.HTML,
    )


@app.on_message(filters.command("index") & filters.private)
async def index_command(client: Client, message: Message):
    if not await begin_session(message, MODE_INDEX):
        return
    await message.reply_text(
        "📑 <b>Index Builder</b>\n\n"
        "<b>Step 1/3:</b> Forward the <b>first message</b> of the batch from the channel.\n\n"
        "<i>Nothing is forwarded or deleted; only an index is posted.</i>",
        parse_mode=ParseMode.HTML,
    )


@app.on_message(filters.command("delete") & filters.private)
async def delete_command(client: Client, message: Message):
    if not await begin_session(message, MODE_DELETE):
        return
    await message.reply_text(
        "🗑 <b>Bulk Delete</b>\n\n"
        "<b>Step 1/2:</b> Forward the <b>first message</b> of the range you want to delete "
        "from the channel.\n\n"
        "<i>The bot must be an admin of that channel with the Delete messages permission.</i>",
        parse_mode=ParseMode.HTML,
    )


def describe_job(job: Session) -> str:
    total = job.end_id - job.start_id + 1
    source = html.escape(job.source_title)
    state = " <i>(stopping…)</i>" if job.cancel else ""
    if job.mode == MODE_FORWARD:
        text = f"📨 Forward <code>#{job.job_id}</code>: {source} → {html.escape(job.target_title)} ({total} IDs)"
    elif job.mode == MODE_DELETE:
        text = f"🗑 Delete <code>#{job.job_id}</code>: {source} ({total} IDs)"
    elif job.mode == MODE_MIX:
        text = f"🔀 Mix forward <code>#{job.job_id}</code>: {source} → {html.escape(job.target_title)} ({total} IDs)"
    elif job.mode == MODE_TXTCHECK:
        text = f"📄 TXT check <code>#{job.job_id}</code>: {source} ({total} IDs)"
    else:
        text = f"📑 Index <code>#{job.job_id}</code>: {source} ({total} IDs)"
    return text + state


def describe_live(task: LiveTask) -> str:
    return (
        f"🔴 Live <code>#{task.task_id}</code>: {html.escape(task.source_title)} → "
        f"{html.escape(task.target_title)} (forwarded {task.forwarded})"
    )


def tasks_view(admin_id: int, heading: str) -> Tuple[str, Optional[InlineKeyboardMarkup]]:
    """Text and buttons listing every task the admin currently has running."""
    lines, rows = [heading, ""], []
    for job in running_jobs.values():
        if job.admin_id == admin_id:
            lines.append(describe_job(job))
            rows.append([InlineKeyboardButton(f"⏹ Stop #{job.job_id}", callback_data=f"task:stop:j:{job.job_id}")])
    for task in live_tasks.values():
        if task.admin_id == admin_id:
            lines.append(describe_live(task))
            rows.append([InlineKeyboardButton(f"🔴 Open panel #{task.task_id}", callback_data=f"task:open:l:{task.task_id}")])
    if not rows:
        return "No tasks are running.", None
    return "\n".join(lines), InlineKeyboardMarkup(rows)


@app.on_message(filters.command("tasks") & filters.private & admin_filter)
async def tasks_command(client: Client, message: Message):
    text, markup = tasks_view(message.from_user.id, "📋 <b>Running tasks</b>")
    await message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=markup)


@app.on_message(filters.command(["stop", "cancel"]) & filters.private & admin_filter)
async def stop_command(client: Client, message: Message):
    user_id = message.from_user.id
    if user_id in sessions:  # a setup wizard is open: cancel it
        sessions.pop(user_id, None)
        await message.reply_text("Cancelled. Send /start to see the available commands.")
        return

    jobs = [job for job in running_jobs.values() if job.admin_id == user_id]
    lives = [task for task in live_tasks.values() if task.admin_id == user_id]
    if not jobs and not lives:
        hint = " Saved live tasks can be resumed or discarded with /live." if any(
            d.get("admin_id", d["_id"]) == user_id for d in paused_docs.values()
        ) else ""
        await message.reply_text("There is no active task to stop." + hint)
    elif len(jobs) + len(lives) == 1:  # exactly one task: stop it straight away
        if jobs:
            jobs[0].cancel = True
            await message.reply_text("🛑 Stop requested. The task will halt after the current batch.")
        else:
            lives[0].stop = True
            lives[0].wake.set()
            await message.reply_text("🛑 Stopping live forwarding. No index will be built.")
    else:
        text, markup = tasks_view(user_id, "Which task do you want to stop?")
        await message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=markup)


@app.on_callback_query(admin_filter & filters.regex(r"^task:"))
async def task_callback(client: Client, query: CallbackQuery):
    user_id = query.from_user.id
    _, action, kind, ident = query.data.split(":", 3)
    expired = "This task is no longer running."

    if kind == "j":
        job = running_jobs.get(int(ident))
        if not job or job.admin_id != user_id:
            await query.answer(expired, show_alert=True)
            return
        job.cancel = True
        await query.answer("Stop requested")
        text, markup = tasks_view(user_id, "📋 <b>Running tasks</b>")
        await safe_edit(query.message, text, parse_mode=ParseMode.HTML, reply_markup=markup)
    else:
        task = live_tasks.get(ident)
        if not task or task.admin_id != user_id:
            await query.answer(expired, show_alert=True)
            return
        task.status = await query.message.edit_text(
            live_panel_text(task), parse_mode=ParseMode.HTML, reply_markup=live_panel_markup(task)
        )
        await query.answer()


@app.on_message(filters.command("add") & filters.private)
async def add_admin_command(client: Client, message: Message):
    if message.from_user.id != OWNER_ID:
        await message.reply_text("⛔ Only the owner can add admins.")
        return
    if len(message.command) < 2 or not message.command[1].lstrip("-").isdigit():
        await message.reply_text("Usage: <code>/add &lt;user_id&gt;</code>", parse_mode=ParseMode.HTML)
        return
    user_id = int(message.command[1])
    await admins_col.update_one({"_id": user_id}, {"$set": {"added_by": OWNER_ID}}, upsert=True)
    await message.reply_text(f"✅ Admin added: <code>{user_id}</code>", parse_mode=ParseMode.HTML)


@app.on_message(filters.command("remove") & filters.private)
async def remove_admin_command(client: Client, message: Message):
    if message.from_user.id != OWNER_ID:
        await message.reply_text("⛔ Only the owner can remove admins.")
        return
    if len(message.command) < 2 or not message.command[1].lstrip("-").isdigit():
        await message.reply_text("Usage: <code>/remove &lt;user_id&gt;</code>", parse_mode=ParseMode.HTML)
        return
    user_id = int(message.command[1])
    result = await admins_col.delete_one({"_id": user_id})
    text = "✅ Admin removed." if result.deleted_count else "That user is not an admin."
    await message.reply_text(text)


@app.on_message(filters.command("admins") & filters.private)
async def list_admins_command(client: Client, message: Message):
    if message.from_user.id != OWNER_ID:
        await message.reply_text("⛔ Only the owner can view the admin list.")
        return
    ids = [doc["_id"] async for doc in admins_col.find()]
    lines = [f"👑 Owner: <code>{OWNER_ID}</code>"] + [f"• <code>{i}</code>" for i in ids]
    await message.reply_text("\n".join(lines), parse_mode=ParseMode.HTML)


# ---------------------------------------------------------------------------
# Setup wizard (forwarded messages from the admin)
# ---------------------------------------------------------------------------
COMMANDS = [
    "start", "forward", "mixforward", "live", "daily_schedule", "add_channel", "quick_schedule", "schedules", "index", "delete", "txt_checker", "txt_update", "txt_updet",
    "tasks", "stop", "cancel", "add", "remove", "admins",
]


def index_confirmation(session: Session) -> Tuple[str, InlineKeyboardMarkup]:
    total = session.end_id - session.start_id + 1
    where = "the same channel" if session.target_id == session.source_id else html.escape(session.target_title)
    text = (
        "📋 <b>Please confirm</b>\n\n"
        f"Channel: <b>{html.escape(session.source_title)}</b>\n"
        f"Range: <code>{session.start_id} → {session.end_id}</code> ({total} IDs)\n"
        f"Index will be posted in: <b>{where}</b>\n\n"
        "No messages will be forwarded or deleted."
    )
    markup = InlineKeyboardMarkup([[
        InlineKeyboardButton("✅ Build index", callback_data="idx:start"),
        InlineKeyboardButton("✖ Cancel", callback_data="idx:cancel"),
    ]])
    return text, markup


async def handle_live_target(client: Client, message: Message, session: Session, chat, title: str) -> None:
    """Last wizard step of /live: either re-link a saved task or ask for confirmation."""
    user_id = message.from_user.id

    if session.resume_doc:
        if chat.id != session.resume_doc["target_id"]:
            await message.reply_text("This is not the saved target channel. Forward a message from it.")
            return
        task = LiveTask.from_doc(session.resume_doc)
        sessions.pop(user_id, None)
        paused_docs.pop(task.task_id, None)
        status = await message.reply_text(
            live_panel_text(task, "\n\n▶ Resumed."), parse_mode=ParseMode.HTML, reply_markup=live_panel_markup(task)
        )
        await start_live_task(client, task, status)
        return

    if chat.id == session.source_id:
        await message.reply_text("Target must be a different channel from the source.")
        return
    session.target_id, session.target_title = chat.id, title
    session.step = STEP_AWAIT_CONFIRM
    await message.reply_text(
        "📋 <b>Please confirm</b>\n\n"
        f"Source: <b>{html.escape(session.source_title)}</b>\n"
        f"Target: <b>{html.escape(session.target_title)}</b>\n"
        f"Starts from message: <code>{session.start_id}</code> (included)\n\n"
        "New posts will be forwarded automatically. You decide when it is complete.",
        parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("🔴 Start live", callback_data="live:start"),
            InlineKeyboardButton("✖ Cancel", callback_data="live:cancel"),
        ]]),
    )


async def handle_txt_document(client: Client, message: Message, session: Session) -> None:
    """Receive a TXT file for /txt_checker or /txt_update."""
    user_id = message.from_user.id
    document = message.document
    name = (document.file_name if document else "") or ""
    if not document or not name.lower().endswith(".txt"):
        await message.reply_text("Please send the file as a <b>.txt</b> document.", parse_mode=ParseMode.HTML)
        return
    if document.file_size and document.file_size > MAX_TXT_BYTES:
        await message.reply_text("That file is too large. The limit is 20 MB.")
        return

    downloaded = await with_retry(lambda: client.download_media(message, in_memory=True))
    text = decode_txt(bytes(downloaded.getbuffer()))

    if session.step == STEP_AWAIT_OLD_TXT:
        session.txt_text, session.txt_name = text, name
        session.step = STEP_AWAIT_NEW_TXT
        await message.reply_text(
            f"✅ Old TXT received (<code>{len(parse_txt(text))}</code> lines).\n\n"
            "<b>Step 2/2:</b> Send the <b>new TXT</b> file.",
            parse_mode=ParseMode.HTML,
        )
    elif session.step == STEP_AWAIT_NEW_TXT:
        sessions.pop(user_id, None)
        await run_txt_update(client, message, session, text, name)
    else:  # STEP_AWAIT_TXT: /txt_checker
        session.txt_text, session.txt_name = text, name
        register_job(session, user_id)
        status = await message.reply_text("⏳ Reading the channel…")
        task = asyncio.create_task(run_txt_checker(client, user_id, session, status))
        background_tasks.add(task)
        task.add_done_callback(background_tasks.discard)


@app.on_message(filters.private & admin_filter & ~filters.command(COMMANDS))
async def wizard_handler(client: Client, message: Message):
    session = sessions.get(message.from_user.id)
    if not session or session.step in (STEP_RUNNING, STEP_AWAIT_CONFIRM):
        return

    if session.mode == MODE_DAILY:
        await handle_daily_input(client, message, session)
        return

    if session.step in (STEP_AWAIT_TXT, STEP_AWAIT_OLD_TXT, STEP_AWAIT_NEW_TXT):
        await handle_txt_document(client, message, session)
        return

    origin = get_forward_origin(message)
    if origin is None:
        await message.reply_text("Please forward a message directly from the channel.")
        return
    chat, msg_id = origin
    title = getattr(chat, "title", None) or str(chat.id)

    if session.step == STEP_AWAIT_START:
        if session.mode == MODE_LIVE:
            if session.resume_doc and chat.id != session.resume_doc["source_id"]:
                await message.reply_text("This is not the saved source channel. Forward a message from it.")
                return
            session.source_id, session.source_title, session.start_id = chat.id, title, msg_id
            session.step = STEP_AWAIT_TARGET
            if session.resume_doc:
                intro = f"✅ Source channel <b>{html.escape(title)}</b> re-linked."
            else:
                intro = (
                    f"✅ Live forwarding will start from message <code>{msg_id}</code> "
                    f"of <b>{html.escape(title)}</b> (this message is included)."
                )
            await message.reply_text(
                intro + "\n\n<b>Step 2/2:</b> Forward any message from the <b>target channel</b>.",
                parse_mode=ParseMode.HTML,
            )
            return

        session.source_id, session.source_title, session.start_id = chat.id, title, msg_id
        session.step = STEP_AWAIT_END
        step_label = "2/2" if session.mode == MODE_DELETE else "2/3"
        await message.reply_text(
            f"✅ Start set to message <code>{msg_id}</code> of <b>{html.escape(title)}</b>.\n\n"
            f"<b>Step {step_label}:</b> Forward the <b>last message</b> of the range "
            "from the same channel.",
            parse_mode=ParseMode.HTML,
        )

    elif session.step == STEP_AWAIT_END:
        if chat.id != session.source_id:
            await message.reply_text("This message is from a different channel. Forward it from the same channel.")
            return
        if msg_id < session.start_id:
            await message.reply_text("The last message must come after the first message. Try again.")
            return
        session.end_id = msg_id

        if session.mode == MODE_DELETE:
            session.step = STEP_AWAIT_CONFIRM
            total = session.end_id - session.start_id + 1
            await message.reply_text(
                "⚠️ <b>Confirm deletion</b>\n\n"
                f"Channel: <b>{html.escape(session.source_title)}</b>\n"
                f"Range: <code>{session.start_id} → {session.end_id}</code> ({total} IDs)\n\n"
                "Every message in this range (videos, PDFs, text, everything) will be "
                "<b>permanently deleted</b>. This cannot be undone.",
                parse_mode=ParseMode.HTML,
                reply_markup=InlineKeyboardMarkup([[
                    InlineKeyboardButton("🗑 Delete", callback_data="del:start"),
                    InlineKeyboardButton("✖ Cancel", callback_data="del:cancel"),
                ]]),
            )
            return

        if session.mode == MODE_TXTCHECK:
            session.step = STEP_AWAIT_TXT
            await message.reply_text(
                f"✅ End set to message <code>{msg_id}</code>.\n\n"
                "<b>Step 3/3:</b> Send the <b>new TXT</b> file.",
                parse_mode=ParseMode.HTML,
            )
            return

        session.step = STEP_AWAIT_TARGET
        if session.mode == MODE_INDEX:
            await message.reply_text(
                f"✅ End set to message <code>{msg_id}</code>.\n\n"
                "<b>Step 3/3:</b> Where should the index be posted?\n"
                "• Tap <b>Same channel</b>, or\n"
                "• Forward any message from another channel.",
                parse_mode=ParseMode.HTML,
                reply_markup=InlineKeyboardMarkup([[
                    InlineKeyboardButton("📍 Same channel", callback_data="idx:same"),
                ]]),
            )
            return
        await message.reply_text(
            f"✅ End set to message <code>{msg_id}</code>.\n\n"
            "<b>Step 3/3:</b> Forward any message from the <b>target channel</b>.",
            parse_mode=ParseMode.HTML,
        )

    elif session.step == STEP_AWAIT_TARGET:
        if session.mode == MODE_LIVE:
            await handle_live_target(client, message, session, chat, title)
            return
        if session.mode in (MODE_FORWARD, MODE_MIX) and chat.id == session.source_id:
            await message.reply_text("Target must be a different channel from the source.")
            return
        session.target_id, session.target_title = chat.id, title
        session.step = STEP_AWAIT_CONFIRM

        if session.mode == MODE_INDEX:
            text, markup = index_confirmation(session)
            await message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=markup)
            return

        total = session.end_id - session.start_id + 1
        await message.reply_text(
            "📋 <b>Please confirm</b>\n\n"
            f"Source: <b>{html.escape(session.source_title)}</b>\n"
            f"Target: <b>{html.escape(session.target_title)}</b>\n"
            f"Range: <code>{session.start_id} → {session.end_id}</code> ({total} IDs)"
            + ("\nOrder: by the number each caption starts with" if session.mode == MODE_MIX else ""),
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([[
                InlineKeyboardButton("✅ Start", callback_data="job:start"),
                InlineKeyboardButton("✖ Cancel", callback_data="job:cancel"),
            ]]),
        )


MODE_BY_PREFIX = {"job": (MODE_FORWARD, MODE_MIX), "del": (MODE_DELETE,), "idx": (MODE_INDEX,)}
JOB_RUNNERS = {
    MODE_FORWARD: run_job, MODE_MIX: run_mix_job,
    MODE_DELETE: run_delete_job, MODE_INDEX: run_index_job,
}
EXPIRED_TEXT = "This request has expired. Send /start to see the available commands."


@app.on_callback_query(admin_filter & filters.regex(r"^(job|del|idx):"))
async def job_callback(client: Client, query: CallbackQuery):
    user_id = query.from_user.id
    session = sessions.get(user_id)
    prefix, action = query.data.split(":", 1)

    if not session or session.mode not in MODE_BY_PREFIX[prefix] or session.step == STEP_RUNNING:
        await query.answer(EXPIRED_TEXT, show_alert=True)
        return

    if action == "cancel":
        sessions.pop(user_id, None)
        await query.message.edit_text("Cancelled. Send /start to see the available commands.")
        await query.answer()
        return

    # Index mode: post the index in the same channel as the batch.
    if prefix == "idx" and action == "same":
        if session.step != STEP_AWAIT_TARGET:
            await query.answer(EXPIRED_TEXT, show_alert=True)
            return
        session.target_id, session.target_title = session.source_id, session.source_title
        session.step = STEP_AWAIT_CONFIRM
        text, markup = index_confirmation(session)
        await query.message.edit_text(text, parse_mode=ParseMode.HTML, reply_markup=markup)
        await query.answer()
        return

    if session.step != STEP_AWAIT_CONFIRM:
        await query.answer(EXPIRED_TEXT, show_alert=True)
        return

    register_job(session, user_id)
    await query.answer("Started")
    status = await query.message.edit_text("⏳ Starting…")
    task = asyncio.create_task(JOB_RUNNERS[session.mode](client, user_id, session, status))
    background_tasks.add(task)
    task.add_done_callback(background_tasks.discard)


def confirm_complete_markup(task_id: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[
        InlineKeyboardButton("✅ Yes, build index", callback_data=f"live:do_complete:{task_id}"),
        InlineKeyboardButton("↩ Back", callback_data=f"live:back:{task_id}"),
    ]])


def confirm_stop_markup(task_id: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[
        InlineKeyboardButton("⏹ Yes, stop", callback_data=f"live:do_stop:{task_id}"),
        InlineKeyboardButton("↩ Back", callback_data=f"live:back:{task_id}"),
    ]])


@app.on_callback_query(admin_filter & filters.regex(r"^live:"))
async def live_callback(client: Client, query: CallbackQuery):
    user_id = query.from_user.id
    parts = query.data.split(":")
    action = parts[1]
    ident = parts[2] if len(parts) > 2 else None
    expired = "This request has expired. Send /live to continue."

    # ---- wizard confirmation -------------------------------------------------
    if action in ("start", "cancel"):
        session = sessions.get(user_id)
        if not session or session.mode != MODE_LIVE or session.step != STEP_AWAIT_CONFIRM:
            await query.answer(expired, show_alert=True)
            return
        if action == "cancel":
            sessions.pop(user_id, None)
            await query.message.edit_text("Cancelled. Send /start to see the available commands.")
            await query.answer()
            return
        task = LiveTask(
            task_id=secrets.token_hex(3),
            admin_id=user_id,
            source_id=session.source_id, source_title=session.source_title,
            target_id=session.target_id, target_title=session.target_title,
            start_id=session.start_id, next_id=session.start_id,
        )
        sessions.pop(user_id, None)
        status = await query.message.edit_text(
            live_panel_text(task), parse_mode=ParseMode.HTML, reply_markup=live_panel_markup(task)
        )
        await query.answer("Live forwarding started")
        await start_live_task(client, task, status)
        return

    # ---- start a new task from the saved-tasks screen ---------------------------
    if action == "new":
        if count_admin_tasks(user_id) >= MAX_TASKS_PER_ADMIN:
            await query.answer("You have reached the task limit. Use /tasks.", show_alert=True)
            return
        sessions[user_id] = Session(mode=MODE_LIVE)
        await query.message.edit_text(LIVE_STEP_1, parse_mode=ParseMode.HTML)
        await query.answer()
        return

    # ---- resume / discard a task saved before a restart ---------------------------
    if action in ("resume", "discard"):
        doc = paused_docs.get(ident)
        if not doc or doc.get("admin_id", doc["_id"]) != user_id:
            await query.answer(expired, show_alert=True)
            return
        if action == "resume":
            sessions[user_id] = Session(mode=MODE_LIVE, resume_doc=doc)
            await query.message.edit_text(
                "♻️ <b>Resume live forwarding</b>\n\n"
                f"<b>Step 1/2:</b> Forward any message from the source channel "
                f"(<b>{html.escape(doc['source_title'])}</b>) so the bot can reconnect to it.",
                parse_mode=ParseMode.HTML,
            )
        else:
            await forget_live_task(ident)
            await query.message.edit_text("🗑 The saved live task has been discarded.")
        await query.answer()
        return

    # ---- control panel of a running task --------------------------------------
    task = live_tasks.get(ident)
    if not task or task.admin_id != user_id:
        await query.answer(expired, show_alert=True)
        return

    if action == "ask_complete":
        await query.message.edit_text(
            f"✅ <b>Finish live forwarding</b> <code>#{task.task_id}</code>?\n\n"
            "The bot will forward whatever is still pending, then post the index "
            "and end the task.",
            parse_mode=ParseMode.HTML, reply_markup=confirm_complete_markup(task.task_id),
        )
    elif action == "ask_stop":
        await query.message.edit_text(
            f"⏹ <b>Stop live forwarding</b> <code>#{task.task_id}</code>?\n\n"
            "The task ends and <b>no index</b> is built.",
            parse_mode=ParseMode.HTML, reply_markup=confirm_stop_markup(task.task_id),
        )
    elif action == "back":
        await query.message.edit_text(
            live_panel_text(task), parse_mode=ParseMode.HTML, reply_markup=live_panel_markup(task)
        )
    elif action == "do_complete":
        task.complete = True
        task.wake.set()
        await query.message.edit_text("⏳ Finishing: forwarding the remaining messages and building the index…")
    elif action == "do_stop":
        task.stop = True
        task.wake.set()
        await query.message.edit_text("🛑 Stopping live forwarding…")
    await query.answer()


@app.on_message(filters.channel)
async def source_channel_listener(client: Client, message: Message):
    """Wake the live tasks whose source channel just received a post."""
    for task in live_tasks.values():
        if task.source_id == message.chat.id:
            task.notify(message.id)


@app.on_callback_query(admin_filter & filters.regex(r"^home:"))
async def home_callback(client: Client, query: CallbackQuery):
    """Buttons of the /start menu: each opens the tool in a new message."""
    openers = {"daily": open_hub, "quick": open_quick, "addch": open_add_channel, "list": open_schedules}
    opener = openers.get(query.data.split(":", 1)[1])
    if opener:
        await opener(query.from_user.id, reply_via(query.message))
    await query.answer()


@app.on_callback_query(admin_filter & filters.regex(r"^qs:"))
async def quick_callback(client: Client, query: CallbackQuery):
    user_id = query.from_user.id
    parts = query.data.split(":", 2)
    action = parts[1]
    arg = parts[2] if len(parts) > 2 else None
    session = sessions.get(user_id)
    expired = "This request has expired. Send /quick_schedule to start again."
    show = edit_via(query.message)

    if action == "undo":
        record = quick_sends.pop(arg, None)
        if not record or record["owner"] != user_id:
            await query.answer("This send can no longer be undone.", show_alert=True)
            return
        removed = await remove_posts(client, {"posted": record["posted"]})
        await show(
            heading("↩️", "UNDONE") + f"\n🗑 Removed <code>{removed}</code> post(s) from your channels.",
            InlineKeyboardMarkup([[btn("⚡ Send another", "qs:again"), btn("⬅ Hub", "ds:menu")]]),
        )
        await query.answer("Removed")
        return
    if action == "again":
        await open_quick(user_id, show)
        await query.answer()
        return
    if action == "cancel":
        await open_hub(user_id, show)
        await query.answer()
        return

    if not session or session.mode != MODE_DAILY or not session.ds.get("quick"):
        await query.answer(expired, show_alert=True)
        return
    data = session.ds
    channels = await owner_channels(user_id)
    data["selected"] &= {c["chat_id"] for c in channels}  # channels may have been removed meanwhile

    async def show_confirm() -> None:
        session.step = STEP_QS_CONFIRM
        await show(*quick_confirm_screen(data, channels))

    async def show_selection() -> None:
        await show(
            heading("📡", "CHOOSE CHANNELS") + "\nTap the channels that should get this message:",
            selection_markup(channels, data["selected"], "✔ Done", prefix="qs", cancel_label="↩ Back", cancel_data="qs:seldone"),
        )

    if action == "choose":
        session.step = STEP_QS_SELECT
        await show_selection()
    elif action in ("tg", "all") and session.step == STEP_QS_SELECT:
        if action == "tg":
            data["selected"] ^= {int(arg)}
        else:
            data["selected"] = set() if len(data["selected"]) >= len(channels) else {c["chat_id"] for c in channels}
        await show_selection()
    elif action == "seldone":
        if not data["selected"]:
            await query.answer("Select at least one channel.", show_alert=True)
            return
        await show_confirm()
    elif action == "silent" and session.step == STEP_QS_CONFIRM:
        data["silent"] = not data.get("silent")
        await show_confirm()
    elif action == "edit" and session.step == STEP_QS_CONFIRM:
        session.step = STEP_QS_EDIT
        await show(
            heading("✏️", "EDIT MESSAGE") + "\nSend the new message. It replaces the current one.",
            InlineKeyboardMarkup([[btn("↩ Back", "qs:seldone")]]),
        )
    elif action == "send" and session.step == STEP_QS_CONFIRM:
        if not data["selected"]:
            await query.answer("Select at least one channel.", show_alert=True)
            return
        targets = sorted(data["selected"])
        await show(heading("⚡", "QUICK SEND") + f"\n⏳ Sending to <code>{len(targets)}</code> channel(s)…", None)
        posted, failures = await copy_to_channels(
            client, targets, data["source_chat"], data["source_msg_id"], bool(data.get("silent"))
        )
        sessions.pop(user_id, None)
        titles = {c["chat_id"]: c["title"] for c in channels}
        lines = [
            heading("⚡", "QUICK SEND", "done"),
            f"✅  Sent to <code>{len(posted)}</code> of <code>{len(targets)}</code> channels",
        ]
        if failures:
            lines.append("\n⚠️ <b>Failed</b>")
            lines += [f"•  {html.escape(titles.get(cid, str(cid)))}: <code>{reason}</code>" for cid, reason in failures]
        rows = []
        if posted:
            token = secrets.token_hex(3)
            quick_sends[token] = {"owner": user_id, "posted": posted}
            while len(quick_sends) > 30:
                quick_sends.pop(next(iter(quick_sends)))
            rows.append([btn("🗑 Undo (delete these posts)", f"qs:undo:{token}")])
            lines.append(f"{DIVIDER}\n<i>Undo works until the bot restarts.</i>")
        rows.append([btn("⚡ Send another", "qs:again"), btn("⬅ Hub", "ds:menu")])
        await show("\n".join(lines), InlineKeyboardMarkup(rows))
    else:
        await query.answer(expired, show_alert=True)
        return
    await query.answer()


@app.on_callback_query(admin_filter & filters.regex(r"^ds:"))
async def daily_callback(client: Client, query: CallbackQuery):
    user_id = query.from_user.id
    parts = query.data.split(":", 2)
    action = parts[1]
    arg = parts[2] if len(parts) > 2 else None
    session = sessions.get(user_id)
    in_wizard = bool(session and session.mode == MODE_DAILY)
    expired = "This request has expired. Send /daily_schedule to continue."
    show = edit_via(query.message)

    async def show_menu() -> None:
        await show(*await menu_screen(user_id))

    async def show_detail(schedule_id: str) -> None:
        await show(*await detail_screen(user_id, schedule_id))

    # ---- navigation -----------------------------------------------------------
    if action == "menu":
        await open_hub(user_id, show)
    elif action == "channels":
        sessions.pop(user_id, None)
        await show(*await channels_screen(user_id))
    elif action == "list":
        await open_schedules(user_id, show)
    elif action == "view":
        sessions.pop(user_id, None)
        await show_detail(arg)
    elif action == "cancel":
        await open_hub(user_id, show)
    elif action == "quick":
        await open_quick(user_id, show)

    # ---- channels ---------------------------------------------------------------
    elif action == "addch":
        await open_add_channel(user_id, show)
    elif action == "addch_done":
        if not await owner_channels(user_id):
            await query.answer("Add at least one channel first.", show_alert=True)
            return
        sessions.pop(user_id, None)
        await show_menu()
    elif action == "rmch":
        channel = next((c for c in await owner_channels(user_id) if str(c["chat_id"]) == arg), None)
        if not channel:
            await query.answer(expired, show_alert=True)
            return
        used = sum(1 for s in await owner_schedules(user_id) if channel["chat_id"] in s["channel_ids"])
        await show(
            heading("🗑", "REMOVE CHANNEL") + f"\n<b>{html.escape(channel['title'])}</b>\n\n"
            f"It will also be removed from <code>{used}</code> schedule(s). Posts already in the channel stay.",
            InlineKeyboardMarkup([[btn("🗑 Remove", f"ds:rmchy:{arg}"), btn("↩ Back", "ds:channels")]]),
        )
    elif action == "rmchy":
        chat_id = int(arg)
        await channels_col.delete_one({"_id": f"{user_id}_{chat_id}"})
        for item in await owner_schedules(user_id):
            if chat_id in item["channel_ids"]:
                remaining = [c for c in item["channel_ids"] if c != chat_id]
                await schedules_col.update_one(
                    {"_id": item["_id"]},
                    {"$set": {"channel_ids": remaining, "active": item["active"] and bool(remaining)}},
                )
        await show(*await channels_screen(user_id))

    # ---- new schedule -------------------------------------------------------------
    elif action == "new":
        if not await owner_channels(user_id):
            await query.answer("Add your channels first.", show_alert=True)
            return
        sessions[user_id] = Session(mode=MODE_DAILY, step=STEP_DS_MESSAGE, ds={"selected": set(), "silent": False})
        await show(
            heading("➕", "NEW SCHEDULE") + "\nSend the message that should be posted every day "
            "(text, photo, video, PDF, anything).",
            InlineKeyboardMarkup([[btn("✖ Cancel", "ds:cancel")]]),
        )
    elif action in ("tg", "all", "seldone", "silent", "create", "createnow"):
        if not in_wizard or session.step not in (STEP_DS_SELECT, STEP_DS_CONFIRM):
            await query.answer(expired, show_alert=True)
            return
        data = session.ds
        channels = await owner_channels(user_id)
        if action == "tg":
            data["selected"] ^= {int(arg)}
        elif action == "all":
            data["selected"] = set() if len(data["selected"]) >= len(channels) else {c["chat_id"] for c in channels}
        elif action == "silent":
            data["silent"] = not data.get("silent")
            titles = {c["chat_id"]: c["title"] for c in channels}
            await show(*confirm_screen(data, [titles.get(cid, str(cid)) for cid in sorted(data["selected"])]))
            await query.answer()
            return
        elif action == "seldone":
            if not data["selected"]:
                await query.answer("Select at least one channel.", show_alert=True)
                return
            if data.get("schedule_id"):  # editing the channels of an existing schedule
                schedule_id = data["schedule_id"]
                await schedules_col.update_one({"_id": schedule_id}, {"$set": {"channel_ids": sorted(data["selected"])}})
                sessions.pop(user_id, None)
                await show_detail(schedule_id)
                await query.answer("Saved")
                return
            session.step = STEP_DS_TIME
            await show(
                heading("🕒", "DAILY TIME") + f"\nSend the time to post every day ({TZ_LABEL}), "
                "for example <code>09:00</code> or <code>9:30 pm</code>.",
                InlineKeyboardMarkup([[btn("✖ Cancel", "ds:cancel")]]),
            )
            await query.answer()
            return
        elif action in ("create", "createnow"):
            if session.step != STEP_DS_CONFIRM:
                await query.answer(expired, show_alert=True)
                return
            schedule_id = secrets.token_hex(3)
            doc = {
                "_id": schedule_id, "owner": user_id,
                "source_chat": data["source_chat"], "source_msg_id": data["source_msg_id"],
                "preview": data["preview"], "channel_ids": sorted(data["selected"]),
                "hour": data["hour"], "minute": data["minute"], "silent": bool(data.get("silent")),
                "active": True, "next_run": next_occurrence(data["hour"], data["minute"], utcnow()),
                "posted": {}, "last_run": None, "last_ok": None, "last_total": None, "created": utcnow(),
            }
            await schedules_col.insert_one(doc)
            sessions.pop(user_id, None)
            if action == "createnow":
                task = asyncio.create_task(run_scheduled_post(client, schedule_id, manual=True))
                background_tasks.add(task)
                task.add_done_callback(background_tasks.discard)
            await show_detail(schedule_id)
            await query.answer("Schedule created")
            return
        if session.step == STEP_DS_SELECT:  # refresh the ticks after a toggle
            editing = bool(data.get("schedule_id"))
            prompt = heading("📡", "CHOOSE CHANNELS") + "\n" + (
                "Select the channels:" if editing else
                "✅ Message saved. <b>Do not delete it from this chat</b> while the schedule is running.\n\n"
                "Select the channels that should get it:"
            )
            await show(prompt, selection_markup(channels, data["selected"], "💾 Save" if editing else "Next ➜"))
        await query.answer()
        return

    # ---- edit the message / change the time of an existing schedule ------------------------
    elif action in ("editnext", "editnow"):
        if not in_wizard or session.step != STEP_DS_EDIT_CHOICE:
            await query.answer(expired, show_alert=True)
            return
        data = session.ds
        schedule_id = data["schedule_id"]
        if not await get_schedule(schedule_id, user_id):
            await query.answer("This schedule no longer exists.", show_alert=True)
            return
        await schedules_col.update_one(
            {"_id": schedule_id},
            {"$set": {"source_chat": data["new_chat"], "source_msg_id": data["new_msg_id"], "preview": data["new_preview"]}},
        )
        sessions.pop(user_id, None)
        if action == "editnow":
            await show(heading("✏️", "EDIT MESSAGE", f"#{schedule_id}") + "\n⏳ Updating your channels…", None)
            await run_scheduled_post(client, schedule_id, manual=True)
        await show_detail(schedule_id)
        await query.answer("Message updated")
        return
    elif action in ("viewmsg", "edit", "time"):
        doc = await get_schedule(arg, user_id)
        if not doc:
            await query.answer("This schedule no longer exists.", show_alert=True)
            return
        if action == "viewmsg":
            try:
                await client.copy_message(user_id, doc["source_chat"], doc["source_msg_id"])
            except RPCError:
                await query.answer("The saved message is no longer available. Use Edit message to set a new one.", show_alert=True)
                return
            await query.message.reply_text(
                heading("✉️", "MESSAGE", f"#{arg}") + "\n👆 This is the message of the schedule.",
                parse_mode=ParseMode.HTML,
                reply_markup=InlineKeyboardMarkup([[btn("⬅ Back to schedule", f"ds:view:{arg}")]]),
            )
        elif action == "edit":
            sessions[user_id] = Session(mode=MODE_DAILY, step=STEP_DS_EDIT, ds={"schedule_id": arg})
            await show(
                heading("✏️", "EDIT MESSAGE", f"#{arg}") + "\nSend the new message. It will replace the current one.",
                InlineKeyboardMarkup([[btn("✖ Cancel", f"ds:view:{arg}")]]),
            )
        else:
            sessions[user_id] = Session(mode=MODE_DAILY, step=STEP_DS_TIME, ds={"schedule_id": arg, "retime": True})
            await show(
                heading("🕒", "CHANGE TIME", f"#{arg}")
                + f"\nCurrent time: <code>{doc['hour']:02d}:{doc['minute']:02d}</code> {TZ_LABEL}\n\n"
                "Send the new daily time, for example <code>09:00</code> or <code>9:30 pm</code>.",
                InlineKeyboardMarkup([[btn("✖ Cancel", f"ds:view:{arg}")]]),
            )

    # ---- managing one schedule ------------------------------------------------------
    elif action in ("now", "stop", "resume", "chs", "del", "delposts", "delonly"):
        doc = await get_schedule(arg, user_id)
        if not doc:
            await query.answer("This schedule no longer exists.", show_alert=True)
            return
        if action == "now":
            if arg in running_schedules:
                await query.answer("It is already being posted.", show_alert=True)
                return
            await query.answer("Posting…")
            await run_scheduled_post(client, arg, manual=True)
            await show_detail(arg)
            return
        if action == "stop":
            await schedules_col.update_one({"_id": arg}, {"$set": {"active": False}})
            await show_detail(arg)
        elif action == "resume":
            await schedules_col.update_one(
                {"_id": arg},
                {"$set": {"active": True, "next_run": next_occurrence(doc["hour"], doc["minute"], utcnow())}},
            )
            await show_detail(arg)
        elif action == "chs":
            channels = await owner_channels(user_id)
            existing = {c["chat_id"] for c in channels}
            selected = {cid for cid in doc["channel_ids"] if cid in existing}
            sessions[user_id] = Session(mode=MODE_DAILY, step=STEP_DS_SELECT, ds={"selected": selected, "schedule_id": arg})
            await show(heading("📡", "CHOOSE CHANNELS", f"#{arg}") + "\nSelect the channels:", selection_markup(channels, selected, "💾 Save"))
        elif action == "del":
            await show(
                heading("🗑", "DELETE SCHEDULE", f"#{arg}") + f"\nIt currently has <code>{len(doc.get('posted', {}))}</code> "
                "post(s) in your channels. Do you want them removed as well?",
                InlineKeyboardMarkup([
                    [btn("🗑 Delete schedule + remove posts", f"ds:delposts:{arg}")],
                    [btn("🗑 Delete schedule only", f"ds:delonly:{arg}")],
                    [btn("↩ Back", f"ds:view:{arg}")],
                ]),
            )
        else:  # delposts / delonly
            if action == "delposts":
                await remove_posts(client, doc)
            await schedules_col.delete_one({"_id": arg})
            await show(*await list_screen(user_id))
    await query.answer()


async def main() -> None:
    await app.start()
    scheduler = asyncio.create_task(scheduler_loop(app))
    try:
        await resume_live_tasks(app)
        await idle()
    finally:
        scheduler.cancel()
        await app.stop()


if __name__ == "__main__":
    logger.info("Bulk Forward Bot starting")
    app.run(main())
