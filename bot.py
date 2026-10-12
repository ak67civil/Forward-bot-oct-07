"""
Bulk Channel Forward Bot
------------------------
Copies a range of messages (videos, PDFs, text) from a source channel to a
target channel in their original order, then publishes a topic index in the
target channel.

Flow (admin only, private chat):
    /start -> forward the FIRST message of the range from the source channel
           -> forward the LAST message of the range from the source channel
           -> forward any message from the target channel
           -> confirm -> bot forwards the range and posts the index.

/delete -> forward the FIRST and LAST message of a range from any channel
           -> confirm -> the bot deletes every message in between (video, PDF, text...).
/stop   -> stops whatever task is currently running (forward or delete).

Admin management (owner only): /add <user_id>, /remove <user_id>, /admins

Index caption formats recognised:
    1) Package : <package name>
    2) Subject Name: <subject>  /  Topic Name: <topic>
    3) 🔖 Topic ➾ <topic name>
    4) Topic : <topic name>
"""

import asyncio
import html
import logging
import os
import random
import re
import time
import unicodedata
from dataclasses import dataclass
from typing import Awaitable, Callable, Dict, List, Optional, Tuple

from motor.motor_asyncio import AsyncIOMotorClient
from pyrogram import Client, filters, raw
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
DEFAULT_PACKAGE = "General"
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


@dataclass
class IndexEntry:
    kind: str                # "package" or "subject" (caption format that was detected)
    title: str               # package name or subject name
    topic: Optional[str]     # topic name (subject format only)
    target_msg_id: int       # first message of this entry in the target channel


# (kind, title, topic) - identifies the section a message belongs to
SectionKey = Tuple[str, str, Optional[str]]


sessions: Dict[int, Session] = {}
background_tasks: set = set()

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
        🔖 Topic ➾ <topic>  /  Topic : <topic>           -> ("topic", topic, None)"""
    subject = topic = package = topic_only = None
    for line in (text or "").splitlines():
        line = unicodedata.normalize("NFKC", line)
        if match := SUBJECT_RE.match(line):
            subject = match.group(1).strip()
        elif match := TOPIC_RE.match(line):
            topic = match.group(1).strip()
        elif match := PACKAGE_RE.match(line):
            package = match.group(1).strip()
        elif match := TOPIC_ONLY_RE.match(line):
            topic_only = match.group(1).strip()
    if subject:
        return "subject", subject, topic
    if package:
        return "package", package, None
    if topic_only:
        return "topic", topic_only, None
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
                    if msg.video or msg.document:
                        key = parse_metadata(msg.caption or "") or current_key
                        # A new index entry starts only when the section changes;
                        # it links to the first message of that section.
                        if key != current_key or not entries:
                            entries.append(IndexEntry(*key, new_id))
                        current_key = key

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
            for page in build_index_pages(entries, target_chat):
                await with_retry(
                    lambda page=page: client.send_message(
                        session.target_id, page,
                        parse_mode=ParseMode.HTML,
                        disable_web_page_preview=True,
                    )
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
        sessions.pop(admin_id, None)


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
        sessions.pop(admin_id, None)


# ---------------------------------------------------------------------------
# Commands
# ---------------------------------------------------------------------------
@app.on_message(filters.command("start") & filters.private)
async def start_command(client: Client, message: Message):
    if not await is_admin(message.from_user.id):
        await message.reply_text("⛔ Access restricted. Contact the owner to be added as an admin.")
        return
    existing = sessions.get(message.from_user.id)
    if existing and existing.step == STEP_RUNNING:
        await message.reply_text("A task is already running. Use /stop to stop it.")
        return
    sessions[message.from_user.id] = Session(mode=MODE_FORWARD)
    await message.reply_text(
        "👋 <b>Bulk Forward Bot</b>\n\n"
        "<b>Step 1/3:</b> Forward the <b>first message</b> of the range "
        "from the <b>source channel</b>.",
        parse_mode=ParseMode.HTML,
    )


@app.on_message(filters.command("delete") & filters.private)
async def delete_command(client: Client, message: Message):
    if not await is_admin(message.from_user.id):
        await message.reply_text("⛔ Access restricted. Contact the owner to be added as an admin.")
        return
    existing = sessions.get(message.from_user.id)
    if existing and existing.step == STEP_RUNNING:
        await message.reply_text("A task is already running. Use /stop to stop it.")
        return
    sessions[message.from_user.id] = Session(mode=MODE_DELETE)
    await message.reply_text(
        "🗑 <b>Bulk Delete</b>\n\n"
        "<b>Step 1/2:</b> Forward the <b>first message</b> of the range you want to delete "
        "from the channel.\n\n"
        "<i>The bot must be an admin of that channel with the Delete messages permission.</i>",
        parse_mode=ParseMode.HTML,
    )


@app.on_message(filters.command(["stop", "cancel"]) & filters.private & admin_filter)
async def stop_command(client: Client, message: Message):
    session = sessions.get(message.from_user.id)
    if not session:
        await message.reply_text("There is no active task to stop.")
    elif session.step == STEP_RUNNING:
        session.cancel = True
        await message.reply_text("🛑 Stop requested. The task will halt after the current batch.")
    else:
        sessions.pop(message.from_user.id, None)
        await message.reply_text("Cancelled. Send /start or /delete to begin again.")


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
COMMANDS = ["start", "stop", "cancel", "delete", "add", "remove", "admins"]


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
        await message.reply_text(
            f"✅ End set to message <code>{msg_id}</code>.\n\n"
            "<b>Step 3/3:</b> Forward any message from the <b>target channel</b>.",
            parse_mode=ParseMode.HTML,
        )

    elif session.step == STEP_AWAIT_TARGET:
        if chat.id == session.source_id:
            await message.reply_text("Target must be a different channel from the source.")
            return
        session.target_id, session.target_title = chat.id, title
        session.step = STEP_AWAIT_CONFIRM
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


@app.on_callback_query(admin_filter & filters.regex(r"^(job|del):"))
async def job_callback(client: Client, query: CallbackQuery):
    user_id = query.from_user.id
    session = sessions.get(user_id)
    if not session or session.step != STEP_AWAIT_CONFIRM:
        await query.answer("This request has expired. Send /start or /delete again.", show_alert=True)
        return

    prefix, action = query.data.split(":", 1)
    expected_mode = MODE_DELETE if prefix == "del" else MODE_FORWARD
    if session.mode != expected_mode:
        await query.answer("This request has expired. Send /start or /delete again.", show_alert=True)
        return

    if action == "cancel":
        sessions.pop(user_id, None)
        await query.message.edit_text("Cancelled. Send /start or /delete to begin again.")
        await query.answer()
        return

    session.step = STEP_RUNNING
    await query.answer("Started")
    status = await query.message.edit_text("⏳ Starting…")
    runner = run_delete_job if session.mode == MODE_DELETE else run_job
    task = asyncio.create_task(runner(client, user_id, session, status))
    background_tasks.add(task)
    task.add_done_callback(background_tasks.discard)


if __name__ == "__main__":
    logger.info("Bulk Forward Bot starting")
    app.run()
