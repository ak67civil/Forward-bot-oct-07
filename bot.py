"""
Bulk Channel Forward Bot
------------------------
Copies a range of messages (videos, PDFs, text) from a source channel to a
target channel in their original order and publishes a topic index. It can also
build an index for an existing batch and bulk-delete a range of messages.

Commands (admins, private chat):
    /forward -> forward the FIRST and LAST message of the range from the source
                channel, then any message from the target channel -> confirm.
    /live    -> forward the message to start from (source) and one message of the
                target channel; the bot then forwards every new post as it arrives.
                Tap "Forward Complete" in the task panel to build the index.
    /index   -> forward the FIRST and LAST message of an existing batch, choose
                where the index goes (same channel or another) -> confirm.
    /delete  -> forward the FIRST and LAST message of a range -> confirm -> the
                bot deletes every message in between.
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
import html
import itertools
import logging
import os
import random
import re
import secrets
import time
import unicodedata
from dataclasses import asdict, dataclass, field
from typing import Awaitable, Callable, Dict, List, Optional, Tuple

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

MODE_FORWARD = "forward"
MODE_DELETE = "delete"
MODE_INDEX = "index"
MODE_LIVE = "live"


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
        elif match := TITLE_RE.match(line):
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
# Commands
# ---------------------------------------------------------------------------
HELP_TEXT = (
    "👋 <b>Bulk Forward Bot</b>\n\n"
    "<b>Commands</b>\n"
    "/forward - Copy a range of messages to another channel and post an index\n"
    "/live - Forward new posts as they arrive, then build the index\n"
    "/tasks - Show your running tasks\n"
    "/index - Build an index for an existing batch (no forwarding)\n"
    "/delete - Bulk delete a range of messages from a channel\n"
    "/stop - Stop the running task\n"
    "/start - Show this menu"
)
OWNER_HELP_TEXT = (
    "\n\n<b>Owner only</b>\n"
    "/add &lt;user_id&gt; - Add an admin\n"
    "/remove &lt;user_id&gt; - Remove an admin\n"
    "/admins - List all admins"
)


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
    text = HELP_TEXT + (OWNER_HELP_TEXT if user_id == OWNER_ID else "")
    await message.reply_text(text, parse_mode=ParseMode.HTML)


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
COMMANDS = ["start", "forward", "live", "index", "delete", "tasks", "stop", "cancel", "add", "remove", "admins"]


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


@app.on_message(filters.private & admin_filter & ~filters.command(COMMANDS))
async def wizard_handler(client: Client, message: Message):
    session = sessions.get(message.from_user.id)
    if not session or session.step in (STEP_RUNNING, STEP_AWAIT_CONFIRM):
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
        if session.mode == MODE_FORWARD and chat.id == session.source_id:
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
            f"Range: <code>{session.start_id} → {session.end_id}</code> ({total} IDs)",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([[
                InlineKeyboardButton("✅ Start", callback_data="job:start"),
                InlineKeyboardButton("✖ Cancel", callback_data="job:cancel"),
            ]]),
        )


MODE_BY_PREFIX = {"job": MODE_FORWARD, "del": MODE_DELETE, "idx": MODE_INDEX}
JOB_RUNNERS = {MODE_FORWARD: run_job, MODE_DELETE: run_delete_job, MODE_INDEX: run_index_job}
EXPIRED_TEXT = "This request has expired. Send /start to see the available commands."


@app.on_callback_query(admin_filter & filters.regex(r"^(job|del|idx):"))
async def job_callback(client: Client, query: CallbackQuery):
    user_id = query.from_user.id
    session = sessions.get(user_id)
    prefix, action = query.data.split(":", 1)

    if not session or session.mode != MODE_BY_PREFIX[prefix] or session.step == STEP_RUNNING:
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


async def main() -> None:
    await app.start()
    try:
        await resume_live_tasks(app)
        await idle()
    finally:
        await app.stop()


if __name__ == "__main__":
    logger.info("Bulk Forward Bot starting")
    app.run(main())
