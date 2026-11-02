#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.14"
# dependencies = [
#     "pillow==12.3.0",
#     "prompt-toolkit==3.0.53",  # imported directly, and its internals are relied on: see setup_question
#     "questionary==2.1.1",
#     "rich==15.0.0",
# ]
# ///

# xteink-manager: manage the XTEINK X4's SD card and prepare books for it.
# Copyright (C) 2026 epohs
#
# This program is free software: you can redistribute it and/or modify it under the terms of the GNU General
# Public License as published by the Free Software Foundation, either version 3 of the License, or (at your
# option) any later version.
#
# This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the
# implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License
# for more details.
#
# You should have received a copy of the GNU General Public License along with this program. If not, see
# <https://www.gnu.org/licenses/>.
#
# SPDX-License-Identifier: GPL-3.0-or-later

"""xteink-manager: manage the XTEINK X4's SD card and prepare books for it.

  Add books        prepare new books and copy them onto the card
  Move or rename   books or folders; progress and bookmarks follow
  Remove books     take books off the card; a copy is saved first
  Prepare books    clean and optimize books on the card or this computer
  Back up          the whole card into an archive with checksums and repair data
  Restore          put books back from a backup, each checked first
  Check books      find books that won't open, or verify a backup
  Stats            the library at a glance, and what's been read

Optimize does what the CrossPoint firmware's "Optimize EPUB" does. Clean repairs
archive.org page-scan books and only ever runs on those. The X4 keeps reading
progress by file path, so every move or rename here carries it along, and a replaced
book keeps it when its chapters are the same.

Run it with no arguments for the menu; `xteink-manager --help` is the short guide.
macOS and Linux. Python 3.14+, run through uv.
"""

import argparse
import difflib
import fcntl
import functools
import glob
import hashlib
import html
import io
import json
import logging
import os
import platform
import plistlib
import posixpath
import re
import shlex
import shutil
import signal
import stat
import struct
import subprocess
import sys
import tarfile
import tempfile
import termios
import textwrap
import threading
import time
import traceback
import unicodedata
import xml.parsers.expat
import zipfile
import zlib
from collections import Counter
from compression import zstd
from contextlib import ExitStack, contextmanager, suppress
from dataclasses import dataclass, field
from datetime import UTC, datetime
from pathlib import Path
from urllib.parse import unquote
from xml.etree import ElementTree

import questionary
from PIL import Image, ImageOps
from prompt_toolkit.application import get_app
from prompt_toolkit.completion import Completer, Completion, PathCompleter
from prompt_toolkit.filters import Condition
from prompt_toolkit.key_binding import KeyBindings, merge_key_bindings
from prompt_toolkit.layout import ConditionalContainer, FormattedTextControl, Window
from prompt_toolkit.shortcuts import CompleteStyle
from questionary import Choice, Separator
from questionary.prompts.common import InquirerControl
from rich.console import Console
from rich.markup import escape as esc
from rich.progress import (
    BarColumn,
    Progress,
    SpinnerColumn,
    TaskProgressColumn,
    TextColumn,
    TimeRemainingColumn,
)
from rich.text import Text
from rich.theme import Theme

VERSION = "1.0.0"
PURPOSE = "the X4 e-reader's SD card"   # in the header, so what it's for shows before anything else
PROG = "xteink-manager" if shutil.which("xteink-manager") else "./xteink-manager.py"  # in suggested commands



# ── Settings: edit to taste ───────────────────────────────────────────────────

# The X4 profile from the firmware's web uploader (FilesPage.html). Images are scaled to fit, never up.
SCREEN_WIDTH = 480
SCREEN_HEIGHT = 800
JPEG_QUALITY = 85
GRAYSCALE = True

# Originals and the X4's records are saved here before anything changes, and Back up copies the whole card
# here, unless another folder is picked at Back up's "Save the backup where?". That's remembered in the state file.
DEFAULT_BACKUPS = Path(__file__).resolve().parent / "xteink-backups"  # sorts beside the script

STATE_FILE = Path(os.environ.get("XDG_CONFIG_HOME") or Path.home() / ".config") / "xteink-manager" / "state.json"
LOGS_SPACE = 5 * 10**6        # every run's log together, in logs/ beside the state file; the oldest go first

# Back up packs the card into one archive (tar + zstd) with a SHA-256 checksum list and par2 repair data.
ZSTD_LEVEL = 3                # EPUBs are zip-compressed already: on this library level 3 saved 2.1%, level 19 only 3.0%
PARITY_PERCENT = 10           # par2 repair data, as a % of the archive; 0 turns it off



# ── Constants ─────────────────────────────────────────────────────────────────

IS_MAC = sys.platform == "darwin"
HOME = Path.home()

RUN_LOG_DETAIL = LOGS_SPACE // 5  # past this, a run's log keeps what was shown, asked and changed, not each file
RUN_LOG_LIMIT = 2 * RUN_LOG_DETAIL  # and past this, nothing more: the start of a run leaves room for this much

DEVICE_DIR = ".crosspoint"   # the firmware's own folder at the card's root: caches, progress, recent list
FONTS_DIR = "fonts"          # the X4's own fonts at the card's root, managed from its Fonts page

# The X4's sleep-screen pictures (CrossPoint 1.6.5): one at the card's root, or folders of them it picks from.
SLEEP_FILES = {"sleep.bmp", "sleep-overlay.bmp", "sleep-overlay.png"}
SLEEP_DIRS = {"sleep", ".sleep", "sleep-overlay", ".sleep-overlay"}
WINDOWS_DIRS = {"system volume information", "$recycle.bin"}  # Windows makes these on any drive it sees
SYSTEM_FOLDER = "That's a system folder, not books."

# OS clutter that never belongs on the card.
JUNK_FILES = {".DS_Store", ".apdisk"}

FAT_FAMILY = {"fat", "fat12", "fat16", "fat32", "exfat"}  # "fat": FAT of unknown size
FAT_BAD_NAME = re.compile(r'[\x00-\x1f"*:<>?\\|/]|[ .]$')
FAT_MAX_NAME = 255     # UTF-16 units, as FAT stores long names
FAT_MAX_FILE = 2**32 - 1      # FAT32 can't hold a single file bigger than this
FOUR_GB_FILESYSTEMS = {"msdos", "vfat", "fat", "fat12", "fat16", "fat32"}  # filesystem_of's names for FAT
NAME_ROOM = len("..renaming")  # the longest a temporary name grows a name by (.Name.epub.renaming), so it fits too

# Reader and card names that mean "SD card" (but not "SSD").
SD_HINT = re.compile(r"(?<![A-Za-z])SD(HC|XC)?\b|microSD|(?i:card|reader|MMC)")

# Never a card, a source or a target in their own right.
NEVER_TOUCH = {
    Path(p).resolve()
    for p in ("/", "/Users", "/home", "/Volumes", "/media", "/mnt", "/run/media", "/System", "/Library",
              "/Applications", "/private", "/usr", "/var", "/etc", "/opt", "/bin", "/sbin", "/tmp", HOME)
}

BACK = object()       # a task returns this when the user backs out to the menu
QUIT = object()       # the menu's Quit, which Esc also picks


@dataclass
class Run:
    """What this run knows besides its options, in one place: main() starts it fresh."""
    interactive: bool = True           # False when there's no terminal to ask in
    backups: Path = DEFAULT_BACKUPS    # where backups go: the default, or the folder picked (from the state file)
    day: str = ""                      # the date the task under way started; all its backups go under it
    task: str = ""                     # the task under way; the line above each question names it
    doing: tuple | None = None         # (verb, what, red): what's being done to what, once the task has picked it
    active: tuple | None = None        # (card, book count) once confirmed: at the right of that line until ejected
    confirmed: tuple | None = None     # (card ID, every drive's ID then) once "Is this the right card?" is Yes
    card_in_use: Card | None = None    # the card being written, so an interrupt can say it wasn't ejected
    work: tuple | None = None          # (books done, total, what was done) during a batch, for a stop to report
    used: dict = field(default_factory=dict)      # card ID: Card, each card picked and not yet ejected
    declined: set = field(default_factory=set)    # IDs of cards whose eject was turned down at the end of a task
    in_menu: bool = False              # tasks return to the menu, so a card can stay mounted for the next
    argv: list = field(default_factory=list)  # how the run was started, for a log turned on partway
    said: set = field(default_factory=set)        # hints already given this run, which needn't come again
    log: Path | None = None            # this run's log, once it's started
    pages: int = 0                     # pages begun this run: each after the first is dated
    clean_pages: bool = False          # Keep scrollback off: each pick from the menu clears the window first
    failed: bool = False               # something went wrong (a red line, or a book left out): the run exits 1
    task_failed: bool = False          # ... in the task under way, so its last line isn't green

    def reset(self) -> None:
        self.__init__()


RUN = Run()
LOG = logging.getLogger("xteink-manager")
LOG.propagate = False
LOG.addHandler(logging.NullHandler())     # until start_log, and with logging off: nothing written, nothing printed
logging.raiseExceptions = False            # a log that can't be written never shows up, let alone stops the run



# ── Terminal UI ───────────────────────────────────────────────────────────────
# A light take on clack: a left rail, ◆ for a question, ◇ once it's answered.

THEME = Theme({
    "rail": "bright_black",
    "hint": "bright_black",
    "accent": "cyan",
    "ok": "green",
    "warn": "yellow",
    "bad": "red",
    "strong": "bold",
    "version": "yellow",
    "heading": "bold blue",
    "term": "green",
})
console = Console(highlight=False, theme=THEME)
errors = Console(stderr=True, highlight=False, theme=THEME)  # warnings, failures and stops: stderr, so they show past a > redirect

QSTYLE = questionary.Style([
    ("qmark", "fg:ansicyan bold"),
    ("question", "bold"),
    ("answer", "fg:ansicyan"),
    ("pointer", "fg:ansicyan bold"),
    ("highlighted", "fg:ansicyan"),
    ("selected", "fg:ansicyan"),
    ("instruction", "fg:ansibrightblack"),
    ("hint", "fg:ansibrightblack"),
    ("disabled", "fg:ansibrightblack"),
    ("text", ""),
    ("rail", "fg:ansibrightblack"),
    ("task", "fg:ansicyan bold"),
    ("danger", "fg:ansired bold"),
    ("subject", "bold"),
    ("accent", "fg:ansicyan"),
    ("pick", "fg:ansigreen"),            # an action that uses the place you're in
    ("nav", "fg:ansiblue"),              # an action that moves around
    ("separator", "fg:ansibrightblack"),
    ("warn", "fg:ansiyellow"),           # an action that needs doing: a card left mounted
])


def _line(mark: str, style: str, body: str | Text = "", to: Console | None = None) -> None:
    """One mark and its text, on `to` (stdout's console unless said). Long text wraps with the rail carried
    down, so the left edge stays unbroken."""
    to = to or console
    if not body:
        to.print(Text(mark, style=style))
        return
    text = body if isinstance(body, Text) else Text.from_markup(body)
    LOG.info("%s  %s", mark, text.plain)
    carry = Text(" " if mark == "└" else "│", style="rail")
    tint = "" if style == "rail" else style  # done, warnings and failures take their mark's color; the rest is plain
    for number, line in enumerate(text.wrap(to, max(20, to.width - 3))):
        lead = Text(mark, style=style) if number == 0 else carry.copy()
        # assemble, not lead + line: + would carry the mark's style under the whole line
        to.print(Text.assemble(lead, "  ", line, style=tint), no_wrap=True, crop=False)


def say(body: str | Text = "") -> None:
    """│  text. Markup is allowed, so pass user data through esc()."""
    _line("│", "rail", body)


def done(body: str | Text) -> None:
    _line("◇", "ok", body)


def warn(body: str | Text) -> None:
    _line("▲", "warn", body, errors)


def mark_failed() -> None:
    """Something went wrong: the task's last line won't be green, and the run exits 1."""
    RUN.failed = RUN.task_failed = True


def fail(body: str | Text) -> None:
    """Something went wrong, said in red."""
    mark_failed()
    _line("■", "bad", body, errors)


def outro(body: str, good: bool = True, to: Console | None = None) -> None:
    """A task's last line. After a failure in that task it's never green."""
    _line("└", "rail", f"[{'ok' if good and not RUN.task_failed else 'warn'}]{body}[/]", to)


def page_break() -> None:
    """Above a page's first line, from the second page on: a line across the terminal with the time, so the
    newest page is easy to find when scrolling back, and matched to the log. With Keep scrollback off, pages
    start on a clean window instead, so there's nothing to mark."""
    if RUN.pages and not RUN.clean_pages:
        stamp = datetime.now().strftime("%H:%M")
        console.print(Text.assemble(("─" * max(0, console.width - len(stamp) - 4) + " ", "rail"), (stamp, "hint"),
                                    (" ──", "rail")), no_wrap=True, crop=True)
    RUN.pages += 1


def clear_screen() -> None:
    """Empty the window and its scrollback, as `clear` does, for Keep scrollback off. It stays the terminal's
    own screen, so a page taller than the window still scrolls back to its top, and whatever ends the run
    stays in view."""
    if console.is_terminal:
        console.file.write("\x1b[H\x1b[2J\x1b[3J")  # home, clear the window, clear the scrollback
        console.file.flush()


def intro() -> None:
    """A page's first lines: the name and what it's for. It names no card: a task picks and confirms one."""
    page_break()
    console.print(Text.assemble(("┌", "rail"), "  ", ("XTEINK Manager", "bold"), ("  ·  ", "rail"), PURPOSE))
    say()


def once(hint: str) -> bool:
    """True the first time a run asks about `hint`: for advice that needn't come again."""
    if hint in RUN.said:
        return False
    RUN.said.add(hint)
    return True


def listing(rows: list[tuple[str, str]], limit: int = 20) -> None:
    """Books, each with why under it (markup): the first `limit` shown, the rest only in the log, so a long list
    stays readable. With logging off, all of them: nothing is left unnamed."""
    limit = limit if RUN.log else len(rows)
    for name, why in rows[:limit]:
        say(f"  [bad]✗[/] {esc(name)}")
        say(f"      [hint]{why}[/]")
    if len(rows) > limit:
        for name, why in rows[limit:]:
            LOG.info("   ✗ %s: %s", name, Text.from_markup(why).plain)
        say(f"  [hint]… {len(rows) - limit} more, named in the log[/]")


def boxed(lines: list[Text], title: str = "") -> None:
    """A small box on the rail, for summaries, with a title in its top edge if given."""
    limit = max(20, console.width - 10)
    for line in lines:
        line.truncate(limit, overflow="ellipsis")
    width = max(max(line.cell_len for line in lines) + 2, len(title) + 4)
    top = f" {title} " + "─" * (width - len(title) - 2) if title else "─" * width
    say(Text("┌" + top + "┐", style="hint"))
    for line in lines:
        say(Text.assemble(("│ ", "hint"), line, " " * (width - 1 - line.cell_len), ("│", "hint")))
    say(Text("└" + "─" * width + "┘", style="hint"))


@dataclass
class Receipt:
    """What a task changed, shown in a box at its end, so it's plain afterwards what's different: a row per book
    or folder (a mark, its path, a note), and counts for what needs no row of its own."""
    rows: list = field(default_factory=list)
    counts: list = field(default_factory=list)

    def add(self, mark: str, name: str, note: str = "") -> None:
        self.rows.append((mark, name, note))


RECEIPT_MARKS = {"+": "ok", "−": "bad", "↻": "accent", "→": "accent", "✎": "accent"}


def show_receipt(title: str, receipt: Receipt, limit: int = 8) -> None:
    """The receipt box, titled with the card or folder, when anything changed: up to `limit` rows, then a count."""
    if not receipt.rows:
        return
    rows = receipt.rows[:limit]
    width = min(48, max(len(nfc(name)) for _, name, _ in rows))
    lines = [Text.assemble((f"{mark} ", RECEIPT_MARKS.get(mark, "")), short(nfc(name), width).ljust(width),
                           ("  " + nfc(note) if note else "", "hint")) for mark, name, note in rows]
    more = [f"… {len(receipt.rows) - limit} more"] if len(receipt.rows) > limit else []
    if more or receipt.counts:
        lines.append(Text(" · ".join(more + receipt.counts), style="hint"))
    boxed(lines, title=f"{title} now")


def progress_bar() -> Progress:
    return Progress(
        TextColumn("[rail]│[/] "),
        SpinnerColumn("dots", style="accent"),
        BarColumn(bar_width=24, complete_style="ok", finished_style="ok", pulse_style="hint"),
        TaskProgressColumn(),
        TextColumn("{task.fields[detail]}", style="strong"),
        TextColumn("[hint]·[/]"),
        TimeRemainingColumn(compact=True),
        TextColumn("{task.fields[note]}", style="hint", markup=False),  # a book's name, as it is
        console=console,
        transient=True,
    )



# ── Prompts ───────────────────────────────────────────────────────────────────
# Each prompt erases itself when answered and leaves one "◇ question  answer" line.

class NeedsTerminal(Exception):
    """A question came up with no terminal to ask it in."""


def _asking(message: str) -> None:
    if not RUN.interactive:
        raise NeedsTerminal(message)


def _answered(message: str, answer: str) -> None:
    LOG.info("◇  %s  → %s", message, answer)
    console.print(Text.assemble(("◇", "ok"), "  ", (message, "hint"), "  ", (answer, "accent")))
    say()


def option(label: str, value, hint: str = "", *, width: int = 0, plain: bool = False,
           disabled: str | None = None, description: str | None = None) -> Choice:
    """A menu choice. `plain` gives a plain-text label, which type-to-filter lists need. `description` shows
    under the list while the choice is highlighted."""
    if plain or disabled:
        return Choice(title=f"{label.ljust(width)}  {hint}".rstrip(), value=value, disabled=disabled)
    title = [("class:text", label.ljust(width))]
    if hint:
        title.append(("class:hint", "  " + hint))
    return Choice(title=title, value=value, description=description)


class StyledTitle(list):
    """A choice's styled title that type-to-filter can still search (it reads title.lower()). `label` is
    what's echoed once it's picked."""

    def __init__(self, tokens: list[tuple[str, str]], label: str):
        super().__init__(tokens)
        self.label = label

    def __str__(self) -> str:
        return "".join(text for _, text in self)

    def lower(self) -> str:
        return str(self).lower()


def action_choice(label: str, value, icon: str, *, style: str = "nav", hint: str = "") -> Choice:
    """A choice that does something, rather than naming something listed: an icon and a color of its own,
    green (`pick`) for using the place you're in, blue (`nav`, purple in many themes) for moving around."""
    label = nfc(label)
    tokens = [(f"class:{style}", f"{icon} {label}")] + ([("class:hint", "  " + hint)] if hint else [])
    return Choice(title=StyledTitle(tokens, label), value=value)


def back(label: str = "Back") -> Choice:
    return action_choice(label, BACK, "←")


def group(heading: str = "") -> Separator:
    """A heading in a list, for a group of choices under it: the menu's On the card, Backups, Info. Without one,
    a line as long, before the menu's Help, Settings and Quit."""
    return Separator(f"{heading} " + "─" * max(3, 22 - len(heading)) if heading else "─" * 23)


def divider() -> Separator:
    """The line between what's listed and the actions under it."""
    return Separator("─" * 13)


def task_line() -> list[tuple[str, str]]:
    """What's being done to what ("Moving  [ History ]/Frost, Charles/"), or before that the task."""
    if RUN.doing:
        verb, what, red = RUN.doing
        return [("class:rail", "│  "), ("class:danger" if red else "class:task", verb), ("", "  "), ("class:subject", what)]
    if RUN.task:
        return [("class:rail", "│  "), ("class:danger" if RUN.task == "Remove books" else "class:task", RUN.task)]
    return []


def card_status() -> list[tuple[str, str]]:
    """The confirmed card, as the header shows it: name, books, free space. Empty once it's gone."""
    if RUN.active is None:
        return []
    card, books = RUN.active
    try:
        free = shutil.disk_usage(card.mount).free
    except OSError:
        return []
    return [("class:accent", card.name), ("class:hint", f" · {plural(books, 'book')} · {human(free)} free")]


def side_by_side(left: list, right: list, width: int) -> list:
    """`left` and `right` on one line, `right` ending where the header's does; `right` on a line of its
    own above when they don't both fit."""
    size = lambda tokens: sum(len(text) for _, text in tokens)
    edge = min(width, 80)
    if not right:
        return left
    if size(left) + 2 + size(right) <= edge:
        return [*(left or [("class:rail", "│")]), ("", " " * (edge - (size(left) or 1) - size(right))), *right]
    return [("class:rail", "│"), ("", " " * max(1, edge - 1 - size(right))), *right, ("", "\n"), *left]


@contextmanager
def doing(verb: str, what: str, *, red: bool = False):
    """While inside, the line above each question says what's being done to what."""
    before, RUN.doing = RUN.doing, (verb, what, red)
    try:
        yield
    finally:
        RUN.doing = before


# Inside a task, every question shows on the line above it what's being done to what, or the task's name
# until something's picked. Esc backs out of every
# question: a list picks its Back choice (up a level in the card's folders, Quit in the menu), a yes/no
# question answers No or goes back where the caller asks, a typed field goes back. Option-arrows and Option-delete send
# Esc plus a key, so a lone Esc waits a moment for a second key, and those still move and delete by word.
def setup_question(question, escape, enter=None):
    app = question.application
    left, right = task_line(), card_status()
    if left or right:
        app.layout.container.children.insert(0, Window(
            FormattedTextControl(lambda: side_by_side(left, right, get_app().output.get_size().columns)),
            dont_extend_height=True, wrap_lines=True))
    bindings = KeyBindings()
    bindings.add("escape")(escape)
    bindings.add("escape", "enter")(lambda event: None)  # Option+Return: Meta+Enter would accept ""
    if enter:
        bindings.add("enter", eager=True)(enter)
    app.key_bindings = merge_key_bindings([app.key_bindings, bindings])
    app.ttimeoutlen = app.timeoutlen = 0.05
    return question


def ask_select(message: str, choices: list[Choice], default=None, *, search: bool = False, echo: bool = True,
               on_escape=BACK, esc_hint: str = "Esc goes back", on_pick=None):
    """Pick one. Esc picks the choice whose value is `on_escape`, the Back choice unless said otherwise;
    with a filter typed, Esc clears the filter first. `on_pick` gets the answer before it's echoed."""
    _asking(message)
    leaves = any(c.value is on_escape for c in choices)
    hints = (["type to filter"] if search else []) + ([esc_hint] if leaves and esc_hint else [])
    for choice in choices:  # typed accents are composed; macOS lists card names decomposed
        if isinstance(choice.title, str):
            choice.title = nfc(choice.title)
    question = questionary.select(
        message, choices=choices, default=default, qmark="◆ ", pointer="●", style=QSTYLE,
        instruction=" · ".join(hints) or " ", use_search_filter=search, use_jk_keys=not search,
        erase_when_done=True,
    )
    control = next(c for c in question.application.layout.find_all_controls() if isinstance(c, InquirerControl))
    # questionary checks the row under the pointer in the whole list, though the pointer counts the rows shown:
    # with a filter typed, the arrows would skip a row past the line
    control.is_selection_valid = lambda: not control.get_pointed_at().disabled  # a Separator is always disabled
    if search:
        show_filter(question, control)

    def escape(event) -> None:
        if control.search_filter:  # the pointer stays on the same choice
            shown = control.filtered_choices
            current = shown[control.pointed_at] if control.pointed_at < len(shown) else None
            control.search_filter = None
            control.pointed_at = control.choices.index(current) if current in control.choices else 0
        elif leaves:
            event.app.exit(result=on_escape)

    def enter(event) -> None:
        if control.search_filter and not filter_matches(control):
            return  # questionary shows the whole list when nothing matches; Enter would pick its first item
        if isinstance(control.get_pointed_at(), Separator):
            return  # clearing a filter can leave the pointer on the line
        control.is_answered = True
        event.app.exit(result=control.get_pointed_at().value)

    value = setup_question(question, escape, enter).unsafe_ask()
    picked = next(c for c in choices if c.value is value)  # by identity: 0 == False would match the wrong one
    label = getattr(picked.title, "label", None) or (picked.title[0][1] if isinstance(picked.title, list)
                                                     else picked.title)
    if on_pick:
        on_pick(value)
    if echo:
        _answered(message, label.strip())
    else:
        LOG.info("◇  %s  → %s", message, label.strip())
    return value


def show_filter(question, control: InquirerControl) -> None:
    """Swap questionary's filter line, "/ f..." under the list, for a plain one right under the question."""
    children = question.application.layout.container.children
    children[:] = [c for c in children if getattr(getattr(c, "content", None), "content", None) is None
                   or getattr(c.content.content, "text", None) != control.get_search_string_tokens]
    at = next(i for i, c in enumerate(children) if getattr(getattr(c, "content", None), "content", None) is control)
    typed = lambda: control.search_filter or ""
    children.insert(at, ConditionalContainer(Window(FormattedTextControl(lambda: filter_line(typed(), filter_matches(control))),
                                                    height=1), filter=Condition(lambda: bool(typed()))))


def filter_matches(control: InquirerControl) -> bool:
    """Whether what's typed matches any choice; the line between contents and actions doesn't count."""
    typed = (control.search_filter or "").lower()
    return any(typed in str(c.title).lower() for c in control.choices if not isinstance(c, Separator))


def filter_line(typed: str, matches: bool) -> list[tuple[str, str]]:
    keys = ("class:hint", "  · Backspace edits · Esc clears")
    if matches:
        return [("", "   "), ("class:hint", "showing names with "), ("class:accent", f'"{typed}"'), keys]
    return [("", "   "), ("class:danger", f'nothing matches "{typed}"'), keys]


def ask_checkbox(message: str, choices: list[Choice]):
    """Pick one or more, or BACK. With nothing to pick, BACK (questionary can't show an empty list)."""
    if not choices:
        return BACK
    _asking(message)
    question = questionary.checkbox(
        message, choices=choices, qmark="◆ ", pointer="●", style=QSTYLE, erase_when_done=True,
        instruction="Space picks · a picks all · Enter confirms · Esc goes back",
        validate=lambda picked: bool(picked) or "Tick at least one with Space, or press Esc to go back.",
    )
    values = setup_question(question, lambda event: event.app.exit(result=BACK)).unsafe_ask()
    if values is not BACK:
        _answered(message, plural(len(values), "picked", "picked"))
    else:
        LOG.info("◇  %s  → Esc, back", message)
    return values


def ask_confirm(message: str, default: bool = True, *, on_escape=False):
    """Yes or No. Esc answers `on_escape`: No, unless the caller needs a way back (BACK)."""
    _asking(message)
    question = questionary.confirm(
        message, default=default, qmark="◆ ", style=QSTYLE, auto_enter=True, erase_when_done=True,
    )
    answer = setup_question(question, lambda event: event.app.exit(result=on_escape)).unsafe_ask()
    if answer is not BACK:
        _answered(message, "Yes" if answer else "No")
    else:
        LOG.info("◇  %s  → Esc, back", message)
    return answer


def typed_field(message: str, hint: str = "", **kwargs):
    """A typed answer, or BACK. Esc closes the suggestions first. The hint sits right after the question."""
    _asking(message)
    question = questionary.text(message, qmark="◆ ", style=QSTYLE, erase_when_done=True,
                                instruction=" · ".join(filter(None, [hint, "Esc goes back"])), **kwargs)

    def escape(event) -> None:
        if event.current_buffer.complete_state:
            event.current_buffer.cancel_completion()
        else:
            event.app.exit(result=BACK)

    answer = setup_question(question, escape).unsafe_ask()
    if answer is BACK:
        LOG.info("◇  %s  → Esc, back", message)
    return answer


def ask_text(message: str, default: str = "", validate=None):
    """Typed text, or BACK."""
    answer = typed_field(message, default=default, validate=validate)
    if answer is not BACK:
        _answered(message, answer)
    return answer


class PlacesCompleter(Completer):
    """Path completion, plus labeled shortcuts: last used, Downloads, Desktop."""

    def __init__(self, places: list[tuple[str, str]], default: str, files: bool):
        self.places = places
        self.default = default
        self.paths = PathCompleter(
            only_directories=not files,
            expanduser=True,
            file_filter=(lambda name: os.path.isdir(name) or name.lower().endswith(".epub")) if files else None,
        )

    def get_completions(self, document, complete_event):
        typed = document.text_before_cursor
        show_all = not typed.strip() or typed == self.default
        for path, label in self.places:
            if path != typed and (show_all or path.casefold().startswith(typed.casefold())):
                yield Completion(path, start_position=-len(typed), display=path, display_meta=label)
        if typed.strip() and not show_all:
            yield from self.paths.get_completions(document, complete_event)


def clean_path(raw: str) -> Path:
    """Accept typed, pasted or dragged-in paths (Terminal escapes spaces when you drag a file in). os.path's
    expanduser, since Path's raises on a "~" that names no home folder, and the field checks every keystroke."""
    text = raw.strip()
    if len(text) >= 2 and text[0] == text[-1] and text[0] in "'\"":
        text = text[1:-1]
    path = Path(os.path.expanduser(text))
    if not path.exists() and "\\" in text:
        path = Path(os.path.expanduser(re.sub(r"\\(.)", r"\1", text)))
    return Path(os.path.abspath(path))


def stray_tilde(raw: str) -> bool:
    """A "~" that names no home folder: "~V" or "~?", a slip for "~/". It would be a folder named "~V" here."""
    text = raw.strip().strip("'\"")
    return text.startswith("~") and os.path.expanduser(text).startswith("~")


def ask_path(message: str, default: str, places: list[tuple[str, str]], *, books: bool, check=None,
             must_exist: bool = True):
    """A path field with Tab completion: a folder, or with `books` also a single .epub, or BACK.
    `check(path)` can return a reason to refuse it. Without `must_exist`, a new folder can be typed."""

    def validate(raw: str):
        if not raw.strip():
            return "Type a path, or press Tab for suggestions."
        if stray_tilde(raw):
            return "Start with ~/ for your home folder."
        path = clean_path(raw)
        if path.is_file() and not (books and is_book_name(path.name)):
            return "Pick a folder or an .epub file." if books else "That's a file. Pick a folder."
        if must_exist and not path.exists():
            return "Can't find that."
        if off_limits(path):
            return "Pick a folder inside this one."
        return (check(path) if check else None) or True

    raw = typed_field(message, "Tab for suggestions, or drag a folder in", default=default, validate=validate,
                      completer=PlacesCompleter(places, default, files=books), complete_style=CompleteStyle.COLUMN)
    if raw is BACK:
        return BACK
    path = clean_path(raw)
    _answered(message, tilde(path))
    return path


class CardCompleter(Completer):
    """Tab completion for paths inside the card, from its root. Matching ignores case and accents' encoding."""

    def __init__(self, root: Path, want: str):
        self.root = root
        self.want = want

    def get_completions(self, document, complete_event):
        typed = document.text_before_cursor
        head, _, tail = typed.rpartition("/")
        folder = resolve_on_card(self.root, head) if head else ""
        if folder is None or not (self.root / folder).is_dir():
            return
        for entry in visible_entries(self.root, folder):
            is_dir = entry.is_dir()
            if not is_dir and (self.want == "folder" or not is_book_name(entry.name)):
                continue
            if nfc(entry.name).casefold().startswith(nfc(tail).casefold()):
                shown = entry.name + ("/" if is_dir else "")
                yield Completion(shown, start_position=-len(tail), display=shown)


def ask_card_path(card: Card, message: str, *, want: str, start: str = "") -> str | None:
    """A book or folder on the card, picked from lists folder by folder (type to filter), or typed with
    Tab completion. `want` is "folder" or "either". Returns the path as the card lists it (a new folder
    may not exist yet), or None to go back."""
    here, up, use, new, typed = start, object(), object(), object(), object()
    while True:
        choices = []
        for entry in visible_entries(card.mount, here):  # what's here, then under a line what can be done
            if entry.is_dir():
                choices.append(option(entry.name + "/", entry.name, plain=True))
            elif want != "folder" and is_book_name(entry.name):
                choices.append(option(entry.name, entry.name, plain=True))
        if choices:
            choices.append(divider())
        if want == "folder":  # where to put something: the pointer starts on the folder it's in
            choices.append(action_choice(f"Into {here}/" if here else "Into the top level", use, "✓", style="pick"))
            choices.append(action_choice("New folder here…", new, "+"))
        elif here:  # what to act on: the folder itself
            choices.append(action_choice(f"All of {posixpath.basename(here)}/", use, "✓", style="pick"))
        if here:
            choices.append(action_choice("Up a level", up, "↑"))
        choices += [action_choice("Type a path…", typed, "›"), back()]
        picked = ask_select(f"{message}  {here + '/' if here else 'top level'}", choices, search=True, echo=False,
                            default=use if want == "folder" else None,
                            on_escape=up if here else BACK,  # one level at a time
                            esc_hint="Esc goes up a level" if here else "Esc goes back")

        if picked is BACK:
            return None
        if picked is up:
            here = posixpath.dirname(here)
            continue
        if picked is typed:
            rel = type_card_path(card, message, want=want, default=f"{here}/" if here else "")
            if rel is None:
                continue
        elif picked is new:
            name = ask_text("New folder name", validate=lambda raw, here=here: name_problem(raw.strip(), card.mount / here)
                            or (SYSTEM_FOLDER if system_path(posixpath.join(here, raw.strip())) else True))
            if name is BACK:
                continue
            rel = posixpath.join(here, name.strip())
        elif picked is use:
            rel = here
        elif (card.mount / here / picked).is_dir():
            here = posixpath.join(here, picked)
            continue
        else:
            rel = posixpath.join(here, picked)
        new_folder = want == "folder" and rel and not (card.mount / rel).is_dir()
        _answered(message, (rel or f"the top level of {card.name}") + ("  (new folder)" if new_folder else ""))
        return rel


def type_card_path(card: Card, message: str, *, want: str, default: str) -> str | None:
    """The same question as a typed path with Tab completion. Esc, or nothing typed, goes back to the list."""

    def validate(raw: str):
        text = raw.strip().strip("/")
        if not text:
            return True
        if system_path(text):
            return SYSTEM_FOLDER
        rel = resolve_on_card(card.mount, text)
        if rel is None:
            parent, name = posixpath.split(text)
            parent_rel = resolve_on_card(card.mount, parent) if parent else ""
            if want == "folder" and parent_rel is not None and (card.mount / parent_rel).is_dir() \
                    and not name_problem(name):
                return True  # a new folder, made when it's used
            return "Not on the card. Tab completes."
        if want == "folder" and not (card.mount / rel).is_dir():
            return "Pick a folder."
        if not (card.mount / rel).is_dir() and not is_book_name(rel):
            return "Pick a folder or an .epub book."
        return True

    raw = typed_field(message, "Tab completes", default=default, validate=validate,
                      completer=CardCompleter(card.mount, want), complete_style=CompleteStyle.COLUMN)
    if raw is BACK:
        return None
    text = raw.strip().strip("/")
    return card_spelling(card.mount, text) if text else None



# ── Small helpers ─────────────────────────────────────────────────────────────

def run(cmd: list[str], *, timeout: float = 60, detail: bool = False) -> subprocess.CompletedProcess:
    """A command's result. A wedged card reader can hang a command, so each has a time limit. A command that
    timed out or isn't installed reads as failed (124, 127). `detail`: one of many (a drive's probe), logged
    as a detail when it succeeds."""
    started = time.monotonic()
    try:
        result = subprocess.run(cmd, stdin=subprocess.DEVNULL, capture_output=True, text=True, errors="replace",
                                check=False, timeout=timeout)
    except subprocess.TimeoutExpired:
        result = subprocess.CompletedProcess(cmd, 124, "", f"{cmd[0]} timed out")
    except FileNotFoundError:
        result = subprocess.CompletedProcess(cmd, 127, "", f"{cmd[0]} isn't installed")
    log_command(result, time.monotonic() - started, detail)
    return result


def log_command(result: subprocess.CompletedProcess, seconds: float, detail: bool = False) -> None:
    """A command in the log: what ran, how it ended, how long it took, and when it failed, the end of what it
    said."""
    level = logging.DEBUG if detail and result.returncode == 0 else logging.INFO
    LOG.log(level, "$  %s  → %s in %.1fs", shlex.join(map(str, result.args)), result.returncode, seconds)
    if result.returncode != 0 and (result.stderr or "").strip():
        for line in result.stderr.strip().splitlines()[-4:]:
            LOG.info("   %s", line)


def natural_key(name: str) -> list:
    """Sort key where 2 comes before 10, case and accent encoding ignored."""
    return [int(part) if part.isdecimal() else part.casefold() for part in re.split(r"(\d+)", nfc(name))]


def human(size: float) -> str:
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if abs(size) < 1000 or unit == "TB":
            return f"{size:.0f} {unit}" if unit in ("B", "KB") else f"{size:.1f} {unit}"
        size /= 1000


def tally(books: int, others: int = 0) -> str:
    """Books (EPUBs) and the other files the X4 opens, said the same way wherever they're counted."""
    return plural(books, "book") + (f" and {plural(others, 'other file')}" if others else "")


def plural(count: int, word: str, many: str | None = None) -> str:
    return f"{count:,} {word if count == 1 else (many or word + 's')}"


def tilde(path) -> str:
    text, home = str(path), str(HOME)
    return "~" + text[len(home):] if text == home or text.startswith(home + os.sep) else text


def short(name: str, width: int = 40) -> str:
    return name if len(name) <= width else name[: width - 1] + "…"


def nfc(text: str) -> str:
    return unicodedata.normalize("NFC", text)


def is_book_name(name: str) -> bool:
    return name.lower().endswith(".epub") and not name.startswith(".")



def today() -> str:
    return datetime.now(UTC).astimezone().date().isoformat()


def skipped_name(name: str) -> bool:
    """Hidden names and Windows' folders: never books, wherever they are."""
    return name.startswith(".") or name.casefold() in WINDOWS_DIRS


def system_path(rel: str) -> bool:
    """A card path the tool never lists, moves or removes: a skipped name anywhere in it, or the X4's fonts."""
    parts = rel.strip("/").split("/")
    return any(skipped_name(p) for p in parts) or parts[0].casefold() == FONTS_DIR


def visible_entries(root: Path, rel: str = "") -> list[os.DirEntry]:
    """The entries of a folder on the card, without system ones, in natural order, folders first."""
    try:
        entries = [e for e in os.scandir(root / rel) if not system_path(posixpath.join(rel, e.name))]
    except OSError:
        return []
    return sorted(entries, key=lambda e: (not e.is_dir(), natural_key(e.name)))


def list_books(root: Path, start: str = "", *, kinds=(".epub",), strict: bool = False) -> list[str]:
    """Every book under root/start as a root-relative path with / separators, exactly as listed.
    Hidden and Windows system folders (the firmware's own among them), the X4's fonts and other drives
    mounted inside are skipped, as system_path skips them. `kinds` are the extensions that count; `strict`
    stops on a folder that can't be read instead of passing over it."""
    books = []
    base = root / start if start else root
    if base.is_file():
        return [start] if posixpath.splitext(base.name)[1].lower() in kinds and not base.name.startswith(".") else []

    def unreadable(error: OSError):
        if strict:
            raise SafetyError(f"Couldn't read {error.filename}; nothing was changed.")

    device = os.stat(base).st_dev
    for dirpath, dirnames, filenames in os.walk(base, onerror=unreadable):
        kept = []
        rel_dir = os.path.relpath(dirpath, root)
        for d in sorted(dirnames, key=natural_key):
            if skipped_name(d) or (rel_dir == "." and d.casefold() == FONTS_DIR):
                continue
            try:
                if os.stat(os.path.join(dirpath, d)).st_dev == device:
                    kept.append(d)
            except OSError as error:
                unreadable(error)
        dirnames[:] = kept
        for name in sorted(filenames, key=natural_key):
            if not name.startswith(".") and posixpath.splitext(name)[1].lower() in kinds:
                books.append(name if rel_dir == "." else f"{rel_dir}/{name}")
    return books


def top_folders(books: list[str]) -> list[str]:
    """The top-level folders that hold books, the genres, in natural order. Books at the top level aren't in one."""
    return sorted({book.split("/")[0] for book in books if "/" in book}, key=natural_key)


def resolve_on_card(root: Path, text: str) -> str | None:
    """Find a typed path on the card, matching each part by name regardless of case or how accents
    are encoded. Returns the path exactly as the card lists it, or None."""
    parts = [p for p in text.strip().strip("/").split("/") if p]
    found = []
    for part in parts:
        folder = root.joinpath(*found)
        try:
            names = os.listdir(folder)
        except OSError:
            return None
        exact = [n for n in names if n == part]
        loose = [n for n in names if nfc(n).casefold() == nfc(part).casefold()]
        match = exact or loose
        if len(match) != 1:
            return None
        found.append(match[0])
    return "/".join(found)


def utf16_length(name: str) -> int:
    """A name's length as FAT and exFAT count it. A name Linux couldn't read as UTF-8 still has one."""
    return len(name.encode("utf-16-le", errors="surrogatepass")) // 2


def name_problem(name: str, folder: Path | None = None) -> str | None:
    """Why a file or folder name can't go on the card, if it can't."""
    if not name:
        return "Type a name."
    if name.startswith("."):
        return "Names can't start with a dot; the X4 hides those."
    if FAT_BAD_NAME.search(name):
        return 'Names can\'t hold  " * : < > ? \\ | /  or end with a dot or space.'
    if (units := utf16_length(name)) > FAT_MAX_NAME - NAME_ROOM:
        return f"Too long for the card: {units} characters, of {FAT_MAX_NAME - NAME_ROOM} at most."
    if folder is not None and resolve_on_card(folder, name) is not None:
        return "That name is already taken there."
    return None


class SafetyError(Exception):
    """Raised when a guard fails; nothing else gets touched after it."""



# ── Remembered paths ──────────────────────────────────────────────────────────

STATE_TYPES = {"library": str, "card_uuid": str, "backups": str, "cards": dict, "debug_log": bool,
               "keep_scrollback": bool}


def load_state() -> dict:
    """What's remembered. Only values of the shape this script writes are kept, so a damaged or hand-edited
    file is at worst forgotten."""
    try:
        state = json.loads(STATE_FILE.read_text())
    except (OSError, ValueError):
        return {}
    if not isinstance(state, dict):
        return {}
    kept = {key: value for key, value in state.items() if isinstance(value, STATE_TYPES.get(key, object))}
    kept["cards"] = {uuid: card for uuid, card in kept.get("cards", {}).items() if isinstance(card, dict)}
    return kept


def save_state(state: dict, **changes) -> bool:
    """Remember these. False when the file couldn't be written: remembering is a convenience, so a run never
    fails over it, but a setting the user picked should say it wasn't kept."""
    state.update(changes)
    try:
        STATE_FILE.parent.mkdir(parents=True, exist_ok=True)
        temp = STATE_FILE.with_name(f"{STATE_FILE.name}.{os.getpid()}.tmp")  # its own, should two runs save at once
        temp.write_text(json.dumps(state, indent=2))
        temp.replace(STATE_FILE)
    except OSError:
        return False
    return True


def remember_card(state: dict, card: Card) -> None:
    entry = state.setdefault("cards", {}).setdefault(card.uuid, {})
    entry.update(name=card.name, updated=datetime.now(UTC).isoformat(timespec="seconds"))
    save_state(state, card_uuid=card.uuid)



# ── Reading and writing EPUBs ─────────────────────────────────────────────────
# A book is handled in memory as {path inside the archive: bytes}, in archive order.

XHTML_EXT_RE = re.compile(r"\.(xhtml|html|htm)$", re.IGNORECASE)
RASTER_EXT_RE = re.compile(r"\.(png|gif|webp|bmp|jpe?g)$", re.IGNORECASE)
RENAMEABLE_EXT_RE = re.compile(r"\.(png|gif|webp|bmp|jpeg)$", re.IGNORECASE)  # .jpg stays .jpg


# Everything zipfile and zlib raise for a damaged or unreadable archive.
BAD_ZIP = (zipfile.BadZipFile, zipfile.LargeZipFile, OSError, EOFError, RuntimeError, NotImplementedError,
           zlib.error, ValueError, KeyError)
# Everything Pillow raises for an image it can't read.
BAD_IMAGE = (OSError, ValueError, SyntaxError, TypeError, struct.error, Image.DecompressionBombError)


def read_epub(raw: bytes) -> dict[str, bytes]:
    """A book's files in archive order, folder entries left out. Raises one of BAD_ZIP. Names are read as UTF-8
    even without the zip's UTF-8 flag, which Info-ZIP's zip leaves off: read as DOS text, "ä" would become "├ñ",
    and the book would be written back under names its own package doesn't list."""
    try:
        archive = zipfile.ZipFile(io.BytesIO(raw), metadata_encoding="utf-8")
    except UnicodeDecodeError:  # a name that isn't UTF-8: really a DOS name, then
        archive = zipfile.ZipFile(io.BytesIO(raw))
    with archive:
        return {info.filename: archive.read(info) for info in archive.infolist() if not info.filename.endswith("/")}


def pack_epub(entries: dict[str, bytes]) -> bytes:
    """mimetype first and stored, as EPUB requires; images stored; everything else deflated."""
    buffer = io.BytesIO()
    with zipfile.ZipFile(buffer, "w") as archive:
        if "mimetype" in entries:
            archive.writestr("mimetype", entries["mimetype"], compress_type=zipfile.ZIP_STORED)
        for name, data in entries.items():
            if name != "mimetype":
                kind = zipfile.ZIP_STORED if RASTER_EXT_RE.search(name) else zipfile.ZIP_DEFLATED  # already compressed
                archive.writestr(name, data, compress_type=kind)
    return buffer.getvalue()


def decode_text(raw: bytes) -> str:
    """Bytes to text: UTF-8 (BOM stripped), UTF-16 with a BOM, else the declared encoding, else Windows-1252."""
    if raw[:3] == b"\xef\xbb\xbf":
        raw = raw[3:]
    elif raw[:2] in (b"\xff\xfe", b"\xfe\xff"):
        return raw.decode("utf-16", "replace")
    try:
        return raw.decode("utf-8")
    except UnicodeDecodeError:
        pass
    head = raw[:512].decode("ascii", "ignore")
    declared = re.search(r'encoding=["\']([^"\']+)["\']', head, re.IGNORECASE) or \
        re.search(r'charset=["\']?([\w.:-]+)', head, re.IGNORECASE)
    encoding = declared.group(1).lower() if declared else "windows-1252"
    try:
        return raw.decode(encoding, "replace")
    except (LookupError, UnicodeError):  # unknown, or a codec that can't replace bad bytes (idna)
        return raw.decode("windows-1252", "replace")


def find_opf(entries: dict[str, bytes]) -> str | None:
    """The package document container.xml names, else the first .opf."""
    if container := entries.get("META-INF/container.xml"):
        found = re.search(r'full-path="([^"]+)"', decode_text(container))
        if found and unquote(found.group(1)) in entries:
            return unquote(found.group(1))
    return next((name for name in entries if name.lower().endswith(".opf")), None)


TEXT_EXT_RE = re.compile(r"\.(xhtml|html|htm|opf|ncx|css|xml)$", re.IGNORECASE)
UTF8_NAMES = {"utf-8", "utf8"}


def relabel_utf8(text: str) -> str:
    """Point an XML declaration, an HTML meta charset or a CSS @charset at UTF-8."""
    def fix(m):
        return m.group(1) + (m.group(2) if m.group(2).lower() in UTF8_NAMES else "utf-8") + m.group(3)

    text = re.sub(r'(<\?xml[^>]*?encoding=["\'])([^"\']+)(["\'])', fix, text, count=1, flags=re.IGNORECASE)
    text = re.sub(r'(<meta\b[^>]*?charset=["\']?)([\w.:-]+)(["\']?)', fix, text, flags=re.IGNORECASE)
    return re.sub(r'\A(\ufeff?@charset\s+["\'])([^"\']+)(["\'])', fix, text, count=1, flags=re.IGNORECASE)


def utf8_entries(entries: dict[str, bytes]) -> dict[str, bytes]:
    """Every text file as UTF-8 that says so. Both steps write text back as UTF-8, and a declaration
    still naming the old encoding makes readers garble it. Files already right stay byte for byte."""
    out = {}
    for name, raw in entries.items():
        if not TEXT_EXT_RE.search(name):
            out[name] = raw
            continue
        text = decode_text(raw)
        fixed = relabel_utf8(text)
        try:
            raw.decode("utf-8")  # a UTF-16 BOM never decodes as UTF-8
            is_utf8 = True
        except UnicodeDecodeError:
            is_utf8 = False
        out[name] = raw if is_utf8 and fixed == text else fixed.encode("utf-8")
    return out


def parses(data: bytes) -> bool:
    """Whether a file is well-formed XML. One in an encoding expat can't read (Shift_JIS, GBK, a misspelled
    name) is judged by its text, read as decode_text reads it."""
    try:
        xml.parsers.expat.ParserCreate().Parse(data, True)
    except xml.parsers.expat.ExpatError:
        return False
    except (ValueError, LookupError):
        try:
            xml.parsers.expat.ParserCreate("utf-8").Parse(decode_text(data).encode("utf-8"), True)
        except xml.parsers.expat.ExpatError:
            return False
    return True


def visible_text(page: str) -> str:
    """A page's readable text: no markup, comments, head, styles, scripts or SVG."""
    page = re.sub(r"<!--[\s\S]*?-->", "", page)
    page = re.sub(r"<(head|style|script|(?:svg:)?svg)\b[\s\S]*?</\1>", "", page, flags=re.IGNORECASE)
    return " ".join(html.unescape(re.sub(r"<[^>]+>", " ", page)).split())


def manifest_tags(opf: str) -> list[tuple[dict[str, str], str]]:
    """Every self-closing <item> in the manifest with an id and an href: its attributes, and the tag as written."""
    tags = []
    for match in re.finditer(r"<(?:\w+:)?item\b([^>]*?)/>", opf):
        attrs = dict(re.findall(r'(\w[-\w]*)="([^"]*)"', match.group(1)))
        if "id" in attrs and "href" in attrs:
            tags.append((attrs, match.group(0)))
    return tags


def manifest_items(opf: str) -> dict[str, dict[str, str]]:
    """id -> attributes, for every self-closing <item> in the manifest."""
    return {attrs["id"]: attrs for attrs, _ in manifest_tags(opf)}


def package_parts(raw_opf: bytes) -> tuple[dict[str, dict[str, str]], list[str]]:
    """The manifest (id -> attributes) and the spine's idrefs, read by an XML parser so any quoting,
    entity or tag form works. A package that won't parse falls back to the regexes."""
    try:
        root = ElementTree.fromstring(raw_opf)
    except (ElementTree.ParseError, ValueError, LookupError):  # also an encoding expat can't read
        opf = decode_text(raw_opf)
        return manifest_items(opf), re.findall(r'<(?:\w+:)?itemref\b[^>]*idref="([^"]+)"', opf)
    named = [(element.tag.rpartition("}")[2], element) for element in root.iter()]
    items = {el.get("id"): dict(el.attrib) for tag, el in named if tag == "item" and el.get("id") and el.get("href")}
    return items, [el.get("idref", "") for tag, el in named if tag == "itemref"]


def spine_paths(entries: dict[str, bytes]) -> list[str]:
    """The reading order as archive paths. When it changes, the X4's saved page no longer points anywhere."""
    opf_name = find_opf(entries)
    if not opf_name:
        return []
    items, spine = package_parts(entries[opf_name])
    base = posixpath.dirname(opf_name)
    return [posixpath.normpath(posixpath.join(base, unquote(items[idref]["href"]))) if idref in items else f"?{idref}"
            for idref in spine]


def opf_metadata(entries: dict[str, bytes]) -> dict:
    """Title, title sort, generator and authors (name, file-as, role) from the package document."""
    opf_name = find_opf(entries)
    opf = decode_text(entries[opf_name]) if opf_name else ""

    def meta(name: str) -> str:
        found = re.search(rf'<(?:\w+:)?meta\b[^>]*\bname="{name}"[^>]*\bcontent="([^"]*)"', opf) or \
            re.search(rf'<(?:\w+:)?meta\b[^>]*\bcontent="([^"]*)"[^>]*\bname="{name}"', opf)
        return html.unescape(found.group(1)).strip() if found else ""

    refines = {}
    for match in re.finditer(r'<(?:\w+:)?meta\b([^>]*)>([^<]*)</(?:\w+:)?meta>', opf):
        attrs = dict(re.findall(r'([\w:-]+)="([^"]*)"', match.group(1)))
        if attrs.get("refines", "").startswith("#") and "property" in attrs:
            refines[(attrs["refines"][1:], attrs["property"])] = html.unescape(match.group(2)).strip()

    authors = []
    for match in re.finditer(r'<dc:creator\b([^>]*)>([^<]*)</dc:creator>', opf):
        attrs = dict(re.findall(r'([\w:-]+)="([^"]*)"', match.group(1)))
        creator_id = attrs.get("id", "")
        role = attrs.get("opf:role") or attrs.get("role") or refines.get((creator_id, "role"), "")
        file_as = attrs.get("opf:file-as") or attrs.get("file-as") or refines.get((creator_id, "file-as"), "")
        authors.append({"name": html.unescape(match.group(2)).strip(), "file_as": html.unescape(file_as).strip(),
                        "role": role.strip().lower()})

    title = re.search(r"<dc:title\b[^>]*>([^<]*)</dc:title>", opf)
    return {
        "title": html.unescape(title.group(1)).strip() if title else "",
        "title_sort": meta("calibre:title_sort"),
        "generator": meta("generator"),
        "authors": authors,
    }



# ── Optimize: what the firmware's "Optimize EPUB" does ────────────────────────
# Ported from CrossPoint's web uploader (FilesPage.html, unchanged from 1.6.0 through 1.6.5), as
# faithfully as is practical off-device. Images: flatten transparency onto white, scale to fit
# 480x800, grayscale, baseline JPEG, png/gif/webp/bmp/jpeg renamed to .jpg. Pages: SVG-wrapped
# images unwrapped to <img>, width/height dropped from <img>, defensive CSS added, comments removed.
# Package: media types, svg properties and the cover meta fixed; NCX uid synced; embedded fonts
# dropped (CrossPoint never renders with them).

# Injected verbatim into every page's <head>; a distinctive piece of it marks a book as optimized.
DEFENSIVE_STYLE = (
    '<style type="text/css">img,svg{max-width:100%;height:auto}'
    'body{overflow-wrap:break-word}table{max-width:100%;table-layout:fixed}'
    'pre,code{white-space:pre-wrap;word-wrap:break-word}*{box-sizing:border-box}</style>'
)
OPTIMIZED_MARKER = "table{max-width:100%;table-layout:fixed}pre,code{white-space:pre-wrap"

FONT_EXT_RE = re.compile(r"\.(ttf|otf|woff2?|eot)$", re.IGNORECASE)
FONT_MEDIA_TYPE_RE = re.compile(
    r"^(font/|application/font-|application/x-font-|application/vnd\.ms-(opentype|fontobject)$)", re.IGNORECASE)
# An @font-face rule, allowing comments or whitespace between the at-keyword and its block.
FONT_FACE_RE = re.compile(r"@font-face(?:\s|/\*[\s\S]*?\*/)*\{[^{}]*\}", re.IGNORECASE)


@dataclass
class OptimizeSettings:
    quality: int = JPEG_QUALITY
    strip_fonts: bool = True
    strip_comments: bool = True


def is_optimized(entries: dict[str, bytes]) -> bool:
    return any(XHTML_EXT_RE.search(name) and OPTIMIZED_MARKER in decode_text(raw) for name, raw in entries.items())


def xml_escape(text: str) -> str:
    return text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace('"', "&quot;")


def rewrite_renamed_refs(text: str, renamed: dict[str, str]) -> str:
    """Every renamed image's file name becomes its .jpg name: the firmware's plain substitution."""
    for old_path, new_path in renamed.items():
        old_name, new_name = posixpath.basename(old_path), posixpath.basename(new_path)
        if old_name != new_name:
            text = text.replace(old_name, new_name)
    return text


SVG_ELEMENT_RE = re.compile(r"<(?:svg:)?svg\b[^>]*>[\s\S]*?</(?:svg:)?svg>", re.IGNORECASE)
SVG_LAST_IMAGE_RE = re.compile(r'<(?:svg:)?image\b[^>]*(?:xlink:)?href=["\']([^"\']+)["\'][^>]*/?>\s*</(?:svg:)?svg>$',
                               re.IGNORECASE)


def unwrap_svg_images(text: str) -> str:
    """Each <svg> that ends in an <image> becomes a plain <img>, which is what makes SVG-only covers
    show. One element at a time, as the firmware's DOM version does."""
    def unwrap(match):
        image = SVG_LAST_IMAGE_RE.search(match.group(0))
        return f'<img style="max-width:100%;height:auto" src="{image.group(1)}" alt="" />' if image else match.group(0)

    return SVG_ELEMENT_RE.sub(unwrap, text)


def strip_img_dimensions(text: str) -> str:
    def clean(match):
        tag = re.sub(r'\s+width\s*=\s*["\'][^"\']*["\']', "", match.group(0), flags=re.IGNORECASE)
        return re.sub(r'\s+height\s*=\s*["\'][^"\']*["\']', "", tag, flags=re.IGNORECASE)
    return re.sub(r"<img\b[^>]*>", clean, text, flags=re.IGNORECASE)


def inject_defensive_style(text: str) -> str:
    """Before </head>, once. Guarded on the block itself, so a re-run never adds a second one."""
    if DEFENSIVE_STYLE in text or "</head>" not in text:
        return text
    return text.replace("</head>", DEFENSIVE_STYLE + "</head>", 1)


def fix_opf(text: str) -> str:
    """Image media types that still say png/gif/webp/bmp, 'svg' item properties, the cover meta."""
    text = re.sub(r'(<(?:\w+:)?item\b[^>]*href="[^"]+\.jpg"[^>]*)media-type="image/(?:png|gif|webp|bmp)"',
                  r'\1media-type="image/jpeg"', text, flags=re.IGNORECASE)
    text = re.sub(r'(<(?:\w+:)?item\b[^>]*)media-type="image/(?:png|gif|webp|bmp)"([^>]*href="[^"]+\.jpg")',
                  r'\1media-type="image/jpeg"\2', text, flags=re.IGNORECASE)

    # The X4 has no SVG renderer: drop the 'svg' token, and the attribute if it was the only one.
    def strip_svg(match):
        kept = [p for p in match.group(1).split() if p != "svg"]
        return f' properties="{" ".join(kept)}"' if kept else ""

    text = re.sub(r'\s+properties="([^"]*)"', strip_svg, text)
    return ensure_cover_meta(text)


def ensure_cover_meta(opf: str) -> str:
    """Make sure <meta name="cover" content="<image item id>"/> exists and names a plain id."""
    patterns = [
        r'<(?:\w+:)?item[^>]+id="([^"]+)"[^>]+properties="[^"]*cover-image[^"]*"',
        r'<(?:\w+:)?item[^>]+properties="[^"]*cover-image[^"]*"[^>]+id="([^"]+)"',
        r'<(?:\w+:)?item[^>]*id="([^"]+)"[^>]*href="[^"]*cover[^"]*"[^>]*media-type="image/',
        r'<(?:\w+:)?item[^>]*href="[^"]*cover[^"]*"[^>]*id="([^"]+)"[^>]*media-type="image/',
        r'<(?:\w+:)?item[^>]*id="([^"]*cover[^"]*)"[^>]*media-type="image/',
        r'<(?:\w+:)?item[^>]*media-type="image/[^"]*"[^>]*id="([^"]*cover[^"]*)"',
    ]
    cover_id = next((m.group(1) for p in patterns if (m := re.search(p, opf, re.IGNORECASE))), None)
    if not cover_id:
        return opf

    tag = f'<meta name="cover" content="{xml_escape(cover_id)}" />'
    existing = re.search(r'<(?:\w+:)?meta\s+name=["\']cover["\']\s+content=["\']([^"\']+)["\']', opf, re.IGNORECASE) or \
        re.search(r'<(?:\w+:)?meta\s+content=["\']([^"\']+)["\']\s+name=["\']cover["\']', opf, re.IGNORECASE)
    if existing:
        if existing.group(1) == cover_id and "/" not in existing.group(1):
            return opf
        opf = re.sub(r'<(?:\w+:)?meta\s+name=["\']cover["\']\s+content=["\'][^"\']+["\']\s*/?>',
                     lambda m: tag, opf, flags=re.IGNORECASE)
        return re.sub(r'<(?:\w+:)?meta\s+content=["\'][^"\']+["\']\s+name=["\']cover["\']\s*/?>',
                      lambda m: tag, opf, flags=re.IGNORECASE)

    end = opf.find("</metadata>")
    if end == -1:
        return opf
    return opf[:end] + f'    <meta name="cover" content="{xml_escape(cover_id)}"/>\n  </metadata>' + \
        opf[end + len("</metadata>"):]


def extract_identifier(opf: str) -> str | None:
    """The package's unique identifier: synced into the NCX's dtb:uid, and how Add spots a different
    book with the same name."""
    uid = re.search(r'<(?:\w+:)?package[^>]*unique-identifier=["\']([^"\']+)["\']', opf, re.IGNORECASE)
    if uid:
        found = re.search(rf'<dc:identifier[^>]*id=["\']{re.escape(uid.group(1))}["\'][^>]*>([^<]+)</dc:identifier>',
                          opf, re.IGNORECASE)
        if found:
            return found.group(1).strip()
    found = re.search(r"<dc:identifier[^>]*>([^<]+)<", opf, re.IGNORECASE)
    return found.group(1).strip() if found else None


def sync_ncx_identifier(ncx: str, identifier: str | None) -> str:
    if not identifier:
        return ncx
    tag = f'<meta name="dtb:uid" content="{xml_escape(identifier)}"/>'
    return re.sub(r'<meta\s+name=["\']dtb:uid["\']\s+content=["\'][^"\']*["\']\s*/?>', lambda m: tag, ncx,
                  flags=re.IGNORECASE)


def strip_comments(xml: str) -> tuple[str, int]:
    """Remove <!-- --> comments; CDATA, <?…?> and a DOCTYPE (with any internal subset) stay verbatim.
    The firmware's stripComments. Returns (text, comments removed)."""
    out, i, n, count = [], 0, len(xml), 0
    while i < n:
        nxt = xml.find("<", i)
        if nxt < 0:
            out.append(xml[i:])
            break
        if nxt > i:
            out.append(xml[i:nxt])
        if xml.startswith("<!--", nxt):
            close = xml.find("-->", nxt + 4)
            i = n if close < 0 else close + 3
            count += 1
            continue
        if xml.startswith("<!DOCTYPE", nxt):
            gt = xml.find(">", nxt + 9)
            subset = xml.find("[", nxt + 9)
            if subset < 0 or (gt >= 0 and subset > gt):
                end = n if gt < 0 else gt + 1
            else:
                close = xml.find("]>", subset)
                end = n if close < 0 else close + 2
            out.append(xml[nxt:end])
            i = end
            continue
        for opener, closer in (("<![CDATA[", "]]>"), ("<?", "?>")):
            if xml.startswith(opener, nxt):
                close = xml.find(closer, nxt + len(opener))
                end = n if close < 0 else close + len(closer)
                out.append(xml[nxt:end])
                i = end
                break
        else:
            out.append("<")
            i = nxt + 1
    return "".join(out), count


def resolve_href(base_file: str, href: str) -> str:
    """An href, relative to the file it appears in, as an archive path."""
    rel = unquote(href.split("#", 1)[0])
    if rel.startswith("/"):
        return posixpath.normpath(rel.lstrip("/"))
    base_dir = base_file.rsplit("/", 1)[0] if "/" in base_file else ""
    return posixpath.normpath(posixpath.join(base_dir, rel)) if base_dir else posixpath.normpath(rel)


def collect_font_paths(entries: dict[str, bytes], opf: str | None, opf_name: str | None) -> set[str]:
    """Embedded fonts: by extension, plus manifest items with a font media type."""
    fonts = {name for name in entries if FONT_EXT_RE.search(name)}
    if opf and opf_name:
        for match in re.finditer(r"<(?:\w+:)?item\b[^>]*>", opf, re.IGNORECASE):
            media = re.search(r'media-type=["\']([^"\']+)', match.group(0), re.IGNORECASE)
            href = re.search(r'href=["\']([^"\']+)', match.group(0), re.IGNORECASE)
            if media and href and FONT_MEDIA_TYPE_RE.search(media.group(1)):
                path = resolve_href(opf_name, href.group(1))
                if path in entries:
                    fonts.add(path)
    return fonts


def strip_font_face_rules(css: str) -> tuple[str, int]:
    return FONT_FACE_RE.subn("", css)


def strip_inline_font_faces(page: str) -> tuple[str, int]:
    """@font-face rules inside each <style> block of a page."""
    total = 0

    def fix(match):
        nonlocal total
        css, count = strip_font_face_rules(match.group(2))
        total += count
        return match.group(1) + css + match.group(3)

    return re.sub(r"(<style\b[^>]*>)([\s\S]*?)(</style>)", fix, page, flags=re.IGNORECASE), total


def remove_font_manifest_items(opf: str, font_paths: set[str], opf_name: str) -> str:
    if not font_paths:
        return opf

    def drop(match):
        href = re.search(r'href=["\']([^"\']+)', match.group(0), re.IGNORECASE)
        return "" if href and resolve_href(opf_name, href.group(1)) in font_paths else match.group(0)

    return re.sub(r"[ \t]*<(?:\w+:)?item\b[^>]*/>[ \t]*\r?\n?", drop, opf, flags=re.IGNORECASE)


def strip_font_encryption_entries(xml: str, font_paths: set[str]) -> tuple[str, str | None]:
    """<EncryptedData> blocks for dropped fonts. Returns ("drop", None) when nothing is left,
    ("keep", xml) when nothing matched, or ("modified", new xml)."""
    removed = 0

    def drop(match):
        nonlocal removed
        uri = re.search(r"<(?:\w+:)?CipherReference\b[^>]*URI=[\"']([^\"']+)", match.group(0), re.IGNORECASE)
        if uri and unquote(uri.group(1)).lstrip("/") in font_paths:
            removed += 1
            return ""
        return match.group(0)

    new = re.sub(r"<(?:\w+:)?EncryptedData\b[\s\S]*?</(?:\w+:)?EncryptedData>\s*", drop, xml, flags=re.IGNORECASE)
    if not removed:
        return "keep", xml
    if not re.findall(r"<(?:\w+:)?(EncryptedData|EncryptedKey)\b", new, re.IGNORECASE):
        return "drop", None
    return "modified", new


def process_image(data: bytes, quality: int) -> bytes:
    """Flatten onto white, scale to fit the screen (never up), grayscale, baseline JPEG.
    Raises one of BAD_IMAGE, so the caller can keep the original bytes."""
    img = Image.open(io.BytesIO(data))
    img.load()
    img = ImageOps.exif_transpose(img)  # a photo's rotation lives in its EXIF, which a re-saved JPEG drops
    if img.mode.startswith("I"):  # 16-bit gray: converting it as it is would clip every pixel to white
        img = img.point(lambda value: value / 256).convert("L")
    if img.mode in ("RGBA", "LA") or (img.mode == "P" and "transparency" in img.info):
        rgba = img.convert("RGBA")
        img = Image.alpha_composite(Image.new("RGBA", rgba.size, (255, 255, 255, 255)), rgba).convert("RGB")
    else:
        img = img.convert("RGB")

    width, height = img.size
    if width > SCREEN_WIDTH or height > SCREEN_HEIGHT:
        scale = min(SCREEN_WIDTH / width, SCREEN_HEIGHT / height)
        img = img.resize((max(1, round(width * scale)), max(1, round(height * scale))), Image.Resampling.LANCZOS)
    if GRAYSCALE:
        img = img.convert("L")  # ITU-R 601-2 luma, the same weights the firmware uses on its canvas

    out = io.BytesIO()
    img.save(out, format="JPEG", quality=quality, optimize=True, progressive=False)  # the X4 wants baseline
    return out.getvalue()


def jpg_names(entries: dict[str, bytes], converted: set[str]) -> dict[str, str]:
    """Converted png/gif/webp/bmp/jpeg images -> .jpg, never onto a name another file already has.
    An image that couldn't be converted keeps its name, so its type stays true."""
    renamed = {}
    taken = {name for name in entries if not (name in converted and RENAMEABLE_EXT_RE.search(name))}
    for name in entries:
        if name in converted and RENAMEABLE_EXT_RE.search(name):
            target, number = RENAMEABLE_EXT_RE.sub(".jpg", name), 1
            while target in taken:
                target = RENAMEABLE_EXT_RE.sub(f"_{number}.jpg", name)
                number += 1
            taken.add(target)
            renamed[name] = target
    return renamed


def optimize(entries: dict[str, bytes], settings: OptimizeSettings) -> tuple[dict[str, bytes], list[str]]:
    """The firmware's Optimize EPUB, on a book in memory. Returns (files, notes)."""
    images = {name for name in entries if RASTER_EXT_RE.search(name)}
    converted = {}
    for name in images:
        try:
            converted[name] = process_image(entries[name], settings.quality)
        except BAD_IMAGE:
            pass  # an image Pillow can't read goes through untouched, under its own name
    renamed = jpg_names(entries, set(converted))
    opf_name = find_opf(entries)
    identifier = book_id(entries)
    font_paths = collect_font_paths(entries, decode_text(entries[opf_name]) if opf_name else None, opf_name) \
        if settings.strip_fonts else set()

    out, comments = {}, 0
    for name, raw in entries.items():
        low = name.lower()
        if name in font_paths:
            continue
        if name in images:
            out[renamed.get(name, name)] = converted.get(name, raw)
        elif XHTML_EXT_RE.search(name):
            text = decode_text(raw)
            if settings.strip_comments:
                text, count = strip_comments(text)
                comments += count
            text = unwrap_svg_images(text)
            text = rewrite_renamed_refs(text, renamed)
            text = strip_img_dimensions(text)
            text = inject_defensive_style(text)
            if settings.strip_fonts:
                text, _ = strip_inline_font_faces(text)
            out[name] = text.encode("utf-8")
        elif low.endswith(".opf"):
            text = fix_opf(rewrite_renamed_refs(decode_text(raw), renamed))
            out[name] = remove_font_manifest_items(text, font_paths, name).encode("utf-8")
        elif low.endswith(".css"):
            text = rewrite_renamed_refs(decode_text(raw), renamed)
            if settings.strip_fonts:
                text, _ = strip_font_face_rules(text)
            out[name] = text.encode("utf-8")
        elif name == "META-INF/encryption.xml" and font_paths:
            action, new_xml = strip_font_encryption_entries(decode_text(raw), font_paths)
            if action != "drop":
                out[name] = new_xml.encode("utf-8") if action == "modified" else raw
        elif low.endswith(".ncx"):
            out[name] = sync_ncx_identifier(rewrite_renamed_refs(decode_text(raw), renamed), identifier).encode("utf-8")
        else:
            out[name] = raw

    notes = [plural(len(converted), "image")] if converted else []
    if font_paths:
        notes.append(f"{plural(len(font_paths), 'font')} removed")
    if comments:
        notes.append(f"{plural(comments, 'comment')} removed")
    return out, notes or ["page styles"]



# ── Clean: archive.org page-scan repair ───────────────────────────────────────
# For the books the Internet Archive generates from page scans ("hocr-to-epub"): one run-on <p> per
# printed page, running headers and page numbers in the text, an empty table of contents, blank and
# duplicate scan images, a dangling cover. Clean rebuilds paragraphs, headings, lists and a table of
# contents, removes the junk, crops or drops duplicate page scans, and merges pages into chapters.
#
# It only ever runs on books that look like those scans. On a well-made book it would do harm: it
# rewrites any page with a single <p> as plain text, drops pages with no text or <img> (an SVG cover
# page, say), and drops any notice.html page and near-blank images. It leaves optimizing to optimize.

def is_unstructured(page: str) -> bool:
    """At most one run-on <p> and no heading: how archive.org lays out each printed page."""
    return len(re.findall(r"<p[^>]*>(.*?)</p>", page, re.DOTALL)) <= 1 and not re.search(r"<h[1-6][ >]", page)


def looks_like_scan(entries: dict[str, bytes]) -> bool:
    """archive.org builds these with ebooklib and names its page scans image_0000_…; on top of that,
    either its notice.html names the Internet Archive or nearly every page (80%, at least 5) is one
    run-on <p>. ebooklib alone proves nothing: other well-made books use it too. Books already cleaned
    no longer qualify, and cleaning them again would change nothing anyway."""
    if "ebook-lib" not in opf_metadata(entries)["generator"].lower():
        return False
    if not any(re.search(r"(^|/)image_\d{4}_", name) for name in entries):
        return False
    notice = next((n for n in entries if posixpath.basename(n).lower() == "notice.html"), None)
    if notice and re.search(r"internet archive|archive\.org", decode_text(entries[notice]), re.IGNORECASE):
        return True
    pages = [n for n in entries if XHTML_EXT_RE.search(n) and posixpath.basename(n).lower() not in ("nav.xhtml",
                                                                                                   "notice.html")]
    return len(pages) >= 5 and sum(is_unstructured(decode_text(entries[n])) for n in pages) >= 0.8 * len(pages)


ALLCAPS_HEADING_RE = re.compile(r"(?<![A-Za-z0-9])([A-Z][A-Z0-9 \-&'’,]{2,58}[A-Z])(?=\s+[A-Z][a-z])")
# Some books style section titles as dot-prefixed lowercase runs (".simple snare"); the lookbehind
# enforces a sentence boundary, and the capital after it starts the section's first sentence.
DOT_HEADING_RE = re.compile(r"(?:(?<=^)|(?<=[.!?]))\s*\.\s?([a-z][a-z0-9 '&,\-]{3,50}?)(?=\s+[A-Z0-9])")
# A running header glued to a page's first words: "American Yew 2 of the hemlock…". Words like
# Figure or Chapter are excluded where it's used, so real references survive.
LEADING_TITLENUM_RE = re.compile(r"^((?:[A-Z][A-Za-z'’\-]+[ ,]+){1,5})(\d{1,3})[.,]? (?=[a-z])")
TITLENUM_REFERENCE_WORDS = {"figure", "table", "chapter", "page", "plate", "fig", "no", "part", "section", "vol",
                            "volume", "step", "item", "route"}
TRAILING_PAGENUM_RE = re.compile(r"\s+\d{1,3}-\d{1,3}\s*$")
TRAILING_LONE_NUM_RE = re.compile(r"(?<=[.!?])\s+\d{1,4}\s*$")
LEADING_PAGENUM_RE = re.compile(r"^\s*-?\s*\d{1,3}\s*-?\s+(?=[A-Z])")
LEADING_COLON_TITLE_RE = re.compile(r"^\s*([A-Za-z][A-Za-z &'\-]{2,40}):\s")

# OCR noise: specks misread as diamonds, squares or pointers, DEL, soft hyphens, zero-width characters
# and U+FFFD. None carry meaning and most render as boxes. Real typography is left alone.
OCR_NOISE_RE = re.compile("[\u2666\u25a0\u25a1\u25ba\u25c6\u25cf\x7f\u00ad\u200b\u200c\u200d\ufeff\ufffd]")
LIGATURES = {"\ufb00": "ff", "\ufb01": "fi", "\ufb02": "fl", "\ufb03": "ffi", "\ufb04": "ffl", "\u00a0": " "}

# archive.org books put every printed page in its own file. The firmware pays per spine item when it
# first indexes a book and paginates lazily per file, so a 190-page book stalls on nearly every turn.
CHAPTER_SPLIT_AT_HEADING_MIN = 24 * 1024   # prefer splitting at a heading once a chapter is this big
CHAPTER_HARD_MAX = 96 * 1024               # always split at this size
CHAPTER_MAX_IMAGES = 6                     # the firmware decodes each image at pagination; keep chapters light
SENTENCE_END = tuple('.!?:;"\'”’)')


def is_blank_image(data: bytes) -> bool:
    """Only genuinely empty scans: 99.9% near-white. A colophon with a small imprint is ~98.9%."""
    try:
        img = Image.open(io.BytesIO(data)).convert("L")
    except BAD_IMAGE:
        return False
    hist = img.histogram()
    total = sum(hist)
    return bool(total) and sum(hist[240:]) / total > 0.999


def looks_like_page_scan(data: bytes, text_len: int) -> bool:
    """A tall portrait image of some size, next to plenty of OCR text."""
    try:
        width, height = Image.open(io.BytesIO(data)).size
    except BAD_IMAGE:
        return False
    return height > 0 and width / height < 0.85 and len(data) > 50_000 and text_len > 200


def _row_profile(img) -> list[float]:
    """Each row's share of dark pixels (threshold 128), sampling every other column."""
    gray = img.convert("L")
    width, height = gray.size
    px = gray.load()
    return [sum(1 for x in range(0, width, 2) if px[x, y] < 128) / (width / 2) for y in range(height)]


def _periodicity_score(window: list[float]) -> float:
    """0..1: how text-like (regular light/dark alternation) a band of rows is."""
    n = len(window)
    if n < 40:
        return 1.0
    mean = sum(window) / n
    if mean < 0.005:
        return 1.0  # blank: not a figure
    thresh = max(0.01, mean * 0.5)
    state, transitions = window[0] > thresh, 0
    for value in window[1:]:
        if (value > thresh) != state:
            transitions += 1
            state = value > thresh
    return min(1.0, transitions / (n / 7.0))  # text at ~14px pitch: ~14 transitions per 100 rows


def _longest_ink_run(prof: list[float], top: int, bottom: int, thresh: float = 0.005) -> int:
    """Drawings ink 60+ rows in a row; a line of text or a heading only 10-20."""
    run = best = 0
    for y in range(top, min(bottom, len(prof))):
        run = run + 1 if prof[y] >= thresh else 0
        best = max(best, run)
    return best


def _find_figure_bands(img, win: int = 110, step: int = 25) -> tuple[list[tuple[int, int]], list[float]]:
    """(top, bottom) figure regions on a page, possibly several; none on a text-only page."""
    prof = _row_profile(img)
    height = len(prof)
    low = [start for start in range(0, height - win, step)
           if _periodicity_score(prof[start:start + win]) < 0.45 and sum(prof[start:start + win]) / win > 0.01]
    if not low:
        return [], prof
    runs, run = [], [low[0]]
    for start in low[1:]:
        if start - run[-1] <= step:
            run.append(start)
        else:
            runs.append(run)
            run = [start]
    runs.append(run)

    bands = []
    for r in runs:
        top, bottom = r[0], min(r[-1] + win, height)
        while top < bottom and prof[top] < 0.002:
            top += 1
        while bottom > top and prof[bottom - 1] < 0.002:
            bottom -= 1
        if bottom - top >= 130 and _longest_ink_run(prof, top, bottom) >= 60:
            bands.append((top, bottom))

    # A thin part of a drawing (a stem, a rope) reads as a gap and splits one figure in two. Merge
    # bands a small gap apart; separate figures have a caption and blank space between them.
    merged = []
    for band in bands:
        if merged and band[0] - merged[-1][1] <= 60:
            merged[-1] = (merged[-1][0], band[1])
        else:
            merged.append(band)
    return merged, prof


def _caption_extent(prof: list[float], bottom: int, height: int, max_caption_height: int = 45) -> int:
    """Rows to extend below a figure for a one-line caption, if the next text block is that short."""
    y = bottom
    while y < height and prof[y] < 0.005:
        y += 1
    if y >= height:
        return 0
    start = y
    while y < height and prof[y] >= 0.005:
        y += 1
    return (y - bottom) + 6 if y - start <= max_caption_height else 0


def crop_figures(data: bytes, pad: int = 30) -> tuple[str, list[bytes]]:
    """('TEXT_ONLY', []) for a redundant text scan, ('FIGURE', crops), or ('UNSURE', []) when the
    page is nearly all figure and should stay whole."""
    img = Image.open(io.BytesIO(data))
    img.load()
    bands, prof = _find_figure_bands(img)
    if not bands:
        return "TEXT_ONLY", []
    width, height = img.size
    if sum(b - t for t, b in bands) / height > 0.88:
        return "UNSURE", []
    crops = []
    for top, bottom in bands:
        bottom = min(height, bottom + _caption_extent(prof, bottom, height))
        buffer = io.BytesIO()
        img.crop((0, max(0, top - pad), width, bottom)).convert("L").save(buffer, format="JPEG", quality=85,
                                                                         optimize=True)
        crops.append(buffer.getvalue())
    return "FIGURE", crops


def smart_title(text: str) -> str:
    """Title case without capitals after apostrophes ("When You're Lost", not "When You'Re Lost")."""
    return " ".join(w[:1].upper() + w[1:].lower() if w else w for w in text.split(" "))


def normalize_ocr_text(text: str) -> tuple[str, int]:
    removed = len(OCR_NOISE_RE.findall(text))
    text = OCR_NOISE_RE.sub("", text)
    for ligature, letters in LIGATURES.items():
        text = text.replace(ligature, letters)
    return re.sub(r"  +", " ", text), removed


def discover_running_header(blobs: list[str]) -> str | None:
    """A '<Book Title>: ' prefix repeated across many pages. Only that fixed part is stripped; the
    chapter name after it varies, and guessing where it ends would eat prose."""
    counter = Counter(m.group(1) for blob in blobs if (m := LEADING_COLON_TITLE_RE.match(blob)))
    if not counter:
        return None
    prefix, count = counter.most_common(1)[0]
    return prefix if count >= max(3, round(0.15 * len(blobs))) else None


def reflow_page_text(raw_text: str, header_prefix: str | None, anchor_prefix: str = "sec",
                     stats: dict | None = None) -> tuple[str, bool, list[tuple[str, str]]]:
    """One page's run-on paragraph as headings, paragraphs and lists. Returns (html, changed,
    [(anchor id, heading text)]) for every <h3>, which the table of contents is built from."""
    changed, headings = False, []
    stats = {} if stats is None else stats
    text, noise = normalize_ocr_text(html.unescape(raw_text))
    if noise:
        changed = True
        stats["noise"] = stats.get("noise", 0) + noise

    if header_prefix is not None and (m := re.match(r"^\s*" + re.escape(header_prefix) + r":\s*", text)):
        text, changed = text[m.end():], True
    if m := LEADING_PAGENUM_RE.match(text):
        text, changed = text[m.end():], True
    # A running header and page number glued to the sentence carried over from the previous page.
    if (m := LEADING_TITLENUM_RE.match(text)) and \
            not {w.strip(",").lower() for w in m.group(1).split()} & TITLENUM_REFERENCE_WORDS:
        text, changed = text[m.end():], True
        stats["hdr"] = stats.get("hdr", 0) + 1
    for pattern in (TRAILING_PAGENUM_RE, TRAILING_LONE_NUM_RE):
        new_text = pattern.sub("", text)
        if new_text != text:
            text, changed = new_text, True

    # A short Title-Case fragment right before an ALL-CAPS heading is the chapter title left over
    # from the running header ("Food & Water" before "FINDING FOOD & WATER").
    first_heading = ALLCAPS_HEADING_RE.search(text)
    if first_heading and first_heading.start(1) <= 40:
        lead = text[:first_heading.start(1)].strip()
        words = [w for w in re.split(r"\s+", lead) if re.search(r"[A-Za-z]", w)]
        if lead and words and all(w[0].isupper() or w == "&" for w in words) and not re.search(r"[.!?]", lead):
            text, changed = text[first_heading.start(1):], True

    def is_heading_boundary(pos: int) -> bool:
        """A heading starts the page or follows a sentence end, unlike '…either TRUE North…'."""
        preceding = text[:pos].rstrip()
        return not preceding or preceding[-1] in ".!?:”\"')"

    marks = [(m.start(1), m.end(1), m.group(1).strip()) for m in ALLCAPS_HEADING_RE.finditer(text)
             if is_heading_boundary(m.start(1))]
    marks += [(m.start(), m.end(), m.group(1).strip()) for m in DOT_HEADING_RE.finditer(text)]
    pruned = []
    for start, end, title in sorted(marks):
        if not pruned or start >= pruned[-1][1]:  # overlapping candidates: the earlier one wins
            pruned.append((start, end, title))

    segments, last_end = [], 0
    for start, end, title in pruned:
        if start > last_end:
            segments.append(("text", text[last_end:start].strip()))
        segments.append(("heading", title))
        last_end, changed = end, True
    segments.append(("text", text[last_end:].strip()))

    out = []
    for kind, chunk in segments:
        if not chunk:
            continue
        if kind == "heading":
            anchor = f"{anchor_prefix}_{len(headings)}"
            title = smart_title(chunk)
            headings.append((anchor, title))
            out.append(f'<h3 id="{anchor}">{html.escape(title)}</h3>')
        elif "•" in chunk:
            pieces = re.split(r"\s*•\s*", chunk)
            intro_text, items = pieces[0].strip(), [p.strip() for p in pieces[1:] if p.strip()]
            if intro_text:
                out.append(f"<p>{html.escape(intro_text)}</p>")
            if items:
                out.append("<ul>" + "".join(f"<li>{html.escape(i)}</li>" for i in items) + "</ul>")
                changed = True
        else:
            out.append(f"<p>{html.escape(chunk)}</p>")
    return "".join(out) or "<p></p>", changed, headings


def suppress_artifact_headings(entries: dict[str, bytes], page_headings: dict, notes: list[str]) -> list[frozenset]:
    """Demote 'headings' that recur across many pages: table column headers, not section titles.

    A) exact: the same normalized text 6+ times. B) fuzzy: token-overlap clusters of 5+, only for
    headings with 4+ significant words, so short real sections ("Solar Time", "Standard Time")
    never cluster. Must run before table-scan pages are emptied, while every member is counted.
    Returns the artifact clusters' token sets."""
    def norm(t):
        return " ".join(re.findall(r"[a-z0-9]+", t.lower()))

    def toks(t):
        return frozenset(w for w in re.findall(r"[a-z]+", t.lower()) if len(w) >= 3)

    refs = [(page, hid, text) for page, hs in page_headings.items() for hid, text in hs if text != "Reference Tables"]
    artifacts = {}

    exact = Counter(norm(t) for _, _, t in refs)
    for page, hid, text in refs:
        if exact[norm(text)] >= 6:
            artifacts.setdefault(page, set()).add(hid)

    clusters, artifact_toksets = [], []
    for page, hid, text in refs:
        ts = toks(text)
        if len(ts) < 4:
            continue
        for cluster in clusters:
            union = len(ts | cluster[0])
            if union and len(ts & cluster[0]) / union >= 0.5:
                cluster[1].append((page, hid, text))
                break
        else:
            clusters.append([set(ts), [(page, hid, text)]])
    for tokens, members in clusters:
        if len(members) >= 5:
            artifact_toksets.append(frozenset(tokens))
            for page, hid, _ in members:
                artifacts.setdefault(page, set()).add(hid)

    if not artifacts:
        return artifact_toksets
    demoted = 0
    for page, hids in artifacts.items():
        if page in entries:
            doc = decode_text(entries[page])
            for hid in hids:
                doc, count = re.subn(rf'<h3 id="{re.escape(hid)}">(.*?)</h3>', r"<p>\1</p>", doc, count=1)
                demoted += count
            entries[page] = doc.encode("utf-8")
        page_headings[page] = [(h, t) for h, t in page_headings.get(page, []) if h not in hids]
        if not page_headings[page]:
            page_headings.pop(page)
    notes.append(f"{plural(demoted, 'repeated column-header heading')} demoted")
    return artifact_toksets


def stitch_bodies(bodies: list[str], counter: dict) -> str:
    """Join page bodies, rejoining paragraphs a printed-page break split: one ending mid-sentence
    followed by a lowercase continuation, or a word split at a hyphen (the hyphen is kept, which is
    right for compounds and merely cosmetic otherwise). Headings, lists and images block stitching."""
    out = ""
    for body in bodies:
        prev = re.search(r"<p>([^<]+)</p>\s*$", out)
        nxt = re.match(r"^\s*<p>([^<]+)</p>", body)
        if prev and nxt:
            prev_text, next_text = prev.group(1).rstrip(), nxt.group(1).lstrip()
            hyphen_split = prev_text.endswith("-")
            if hyphen_split or (not prev_text.endswith(SENTENCE_END) and next_text[:1].islower()):
                joiner = "" if hyphen_split else " "
                out = out[:prev.start()] + "<p>" + prev_text + joiner + next_text + "</p>" + body[nxt.end():]
                counter["stitched"] = counter.get("stitched", 0) + 1
                continue
        out += body
    return out


def merge_pages_into_chapters(entries: dict[str, bytes], opf: str, base_dir: str, mergeable: set[str],
                              page_headings: dict, notes: list[str]) -> str:
    """Join runs of consecutive one-page spine documents into chapter files. Rewrites entries and
    page_headings in place; returns the updated package document."""
    tags = manifest_tags(opf)
    id_to_href = {attrs["id"]: attrs["href"] for attrs, _ in tags}
    item_tags = {attrs["id"]: tag for attrs, tag in tags}
    spine_ids = re.findall(r'<itemref\b[^>]*idref="([^"]+)"', opf)

    def full_path(href):
        return posixpath.normpath(posixpath.join(base_dir, href))

    runs, current = [], []
    for iid in spine_ids:
        href = id_to_href.get(iid)
        name = full_path(href) if href else None
        if name and name in mergeable and name in entries:
            current.append((iid, name))
        else:
            if len(current) > 1:
                runs.append(current)
            current = []
    if len(current) > 1:
        runs.append(current)
    if not runs:
        return opf

    def body_of(name):
        m = re.search(r"<body[^>]*>(.*)</body>", decode_text(entries[name]), re.DOTALL)
        return m.group(1) if m else ""

    def head_of(name):
        m = re.search(r"<head[^>]*>.*?</head>", decode_text(entries[name]), re.DOTALL)
        return m.group(0) if m else "<head><title></title></head>"

    sample = re.search(r'media-type="([^"]+)"', item_tags.get(runs[0][0][0]) or "")
    media_type = sample.group(1) if sample else "application/xhtml+xml"

    new_page_headings, chapter_seq, total_merged, stitch_counter = {}, 0, 0, {}
    for run in runs:
        head_template = head_of(run[0][1])
        chapters, names, bodies, size, imgs = [], [], [], 0, 0
        for _, name in run:
            body = body_of(name)
            starts_with_heading = bool(re.match(r"\s*<h3\b", body))
            n_imgs = body.count("<img")
            if bodies and ((starts_with_heading and size >= CHAPTER_SPLIT_AT_HEADING_MIN)
                           or size >= CHAPTER_HARD_MAX or (n_imgs and imgs + n_imgs > CHAPTER_MAX_IMAGES)):
                chapters.append((names, bodies))
                names, bodies, size, imgs = [], [], 0, 0
            names.append(name)
            bodies.append(body)
            size += len(body)
            imgs += n_imgs
        if bodies:
            chapters.append((names, bodies))

        first_iid = run[0][0]
        run_iids = {iid for iid, _ in run}
        chapter_items, chapter_itemrefs = [], []
        for member_names, member_bodies in chapters:
            chapter_seq += 1
            ch_base = f"ch_{chapter_seq:03d}.html"
            ch_name = f"{base_dir}/{ch_base}" if base_dir else ch_base
            while ch_name in entries:  # never clobber a file the book already has
                chapter_seq += 1
                ch_base = f"ch_{chapter_seq:03d}.html"
                ch_name = f"{base_dir}/{ch_base}" if base_dir else ch_base
            ch_id = f"mergedch_{chapter_seq}"

            merged_headings = []
            for n in member_names:
                merged_headings.extend(page_headings.pop(n, []))
            title = merged_headings[0][1] if merged_headings else ""
            head = re.sub(r"<title>.*?</title>", lambda m, t=title: f"<title>{html.escape(t)}</title>",
                          head_template, flags=re.DOTALL)
            doc = ("<?xml version='1.0' encoding='utf-8'?>\n<!DOCTYPE html>\n"
                   '<html xmlns="http://www.w3.org/1999/xhtml" '
                   'xmlns:epub="http://www.idpf.org/2007/ops" lang="en" xml:lang="en">\n'
                   f"{head}\n<body>{stitch_bodies(member_bodies, stitch_counter)}</body>\n</html>")
            entries[ch_name] = doc.encode("utf-8")
            if merged_headings:
                new_page_headings[ch_name] = merged_headings
            chapter_items.append(f'<item href="{ch_base}" id="{ch_id}" media-type="{media_type}"/>')
            chapter_itemrefs.append(f'<itemref idref="{ch_id}"/>')
            for n in member_names:
                entries.pop(n, None)
                total_merged += 1

        for iid in run_iids:  # manifest: merged pages out, chapters in
            if tag := item_tags.get(iid):
                opf = opf.replace(tag, "", 1)
        opf = opf.replace("</manifest>", "  " + "\n  ".join(chapter_items) + "\n  </manifest>", 1)
        # Spine: the first merged page's itemref becomes the chapters; the rest go.
        first_ref = re.compile(rf'<itemref\b[^>]*idref="{re.escape(first_iid)}"[^>]*/>')
        opf = first_ref.sub(lambda m, refs=chapter_itemrefs: "\n    ".join(refs), opf, count=1)
        for iid in run_iids - {first_iid}:
            opf = re.sub(rf'\s*<itemref\b[^>]*idref="{re.escape(iid)}"[^>]*/>', "", opf)

    new_page_headings.update(page_headings)  # pages that never merged keep their headings
    page_headings.clear()
    page_headings.update(new_page_headings)
    if stitch_counter.get("stitched"):
        notes.append(f"{plural(stitch_counter['stitched'], 'paragraph')} rejoined across page breaks")
    notes.append(f"{total_merged} pages → {plural(chapter_seq, 'chapter')}")
    return opf


def build_toc(opf: str, base_dir: str, page_headings: dict, title: str) -> tuple[str | None, str | None, int]:
    """(nav html, ncx navMap, entries) from the generated <h3> anchors in reading order, or
    (None, None, 0) when there are no usable headings."""
    id_to_href = {iid: attrs["href"] for iid, attrs in manifest_items(opf).items()}

    nav_items, nav_points, order, prev_label = [], [], 0, None
    for iid in re.findall(r'<itemref\b[^>]*idref="([^"]+)"', opf):
        href = id_to_href.get(iid)
        if not href:
            continue
        for anchor, text in page_headings.get(posixpath.normpath(posixpath.join(base_dir, href)), []):
            label = text.strip()
            if len(label) < 3 or label == prev_label:
                continue
            prev_label = label
            order += 1
            target = f"{href}#{anchor}"
            nav_items.append(f'        <li><a href="{target}">{html.escape(label)}</a></li>')
            nav_points.append(f'    <navPoint id="np{order}" playOrder="{order}">\n'
                              f"      <navLabel><text>{html.escape(label)}</text></navLabel>\n"
                              f'      <content src="{target}"/>\n'
                              "    </navPoint>")
    if not nav_items:
        return None, None, 0
    nav_html = ('<nav epub:type="toc" id="toc" role="doc-toc">\n'
                f"      <h2>{html.escape(title)}</h2>\n      <ol>\n" + "\n".join(nav_items) + "\n      </ol>\n    </nav>")
    return nav_html, "<navMap>\n" + "\n".join(nav_points) + "\n  </navMap>", order


def prune_dangling_manifest_items(entries: dict[str, bytes], opf: str, base_dir: str, notes: list[str],
                                  removed: frozenset[str] = frozenset()) -> str:
    """Manifest items (and their spine entries) whose file isn't in the archive, a source defect that
    can hang the firmware's indexer. Dead <a href> links to them are unwrapped, content kept."""
    missing = {iid: attrs["href"] for iid, attrs in manifest_items(opf).items()
               if posixpath.normpath(posixpath.join(base_dir, attrs["href"])) not in entries}
    if not missing:
        return opf

    for iid, href in missing.items():
        opf = re.sub(rf'\s*<item\b[^>]*href="{re.escape(href)}"[^>]*/>', "", opf)
        opf = re.sub(rf'\s*<itemref\b[^>]*idref="{re.escape(iid)}"[^>]*/>', "", opf)

    missing_names = {posixpath.basename(href) for href in missing.values()}
    unwrapped = 0

    def unwrap_dead_link(m):
        # Some of these anchors are also a jump target (<a href=dead id="real-anchor">); keep a bare
        # id-only anchor then, or dropping the id would make a second dangling reference.
        nonlocal unwrapped
        unwrapped += 1
        id_m = re.search(r'\bid="([^"]*)"', m.group(1))
        return f'<a id="{id_m.group(1)}"></a>{m.group(2)}' if id_m else m.group(2)

    for name in list(entries):
        if not XHTML_EXT_RE.search(name):
            continue
        doc = original = decode_text(entries[name])
        for base in missing_names:
            doc = re.sub(rf'<a\b([^>]*href="[^"]*{re.escape(base)}"[^>]*)>(.*?)</a>', unwrap_dead_link, doc,
                         flags=re.DOTALL)
        if doc != original:
            entries[name] = doc.encode("utf-8")
    if defects := [href for href in missing.values() if posixpath.normpath(posixpath.join(base_dir, href)) not in removed]:
        notes.append(f"{plural(len(defects), 'listed file')} the book never had dropped"
                     + (f", {plural(unwrapped, 'dead link')} unwrapped" if unwrapped else ""))
    return opf


def rel_to(base_dir: str, path: str) -> str:
    return posixpath.relpath(path, base_dir) if base_dir else path


def clean(entries: dict[str, bytes], book_title: str) -> tuple[dict[str, bytes], list[str]]:
    """archive.org repair on a book in memory. Returns (files, notes); the input is left as it was."""
    entries = dict(entries)
    notes = []

    # Unstructured pages: exactly one <p> and no heading. Already-structured pages are left alone.
    candidate_pages = {}
    for name in entries:
        if not XHTML_EXT_RE.search(name):
            continue
        text = decode_text(entries[name])
        paragraphs = re.findall(r"<p[^>]*>(.*?)</p>", text, re.DOTALL)
        if len(paragraphs) != 1 or re.search(r"<h[1-6][ >]", text):
            continue
        blob = re.sub(r"\s+", " ", re.sub(r"<[^>]+>", " ", paragraphs[0])).strip()
        if blob:
            candidate_pages[name] = (text, blob)

    header_prefix = discover_running_header([html.unescape(blob) for _, blob in candidate_pages.values()])
    if header_prefix:
        notes.append(f"running header “{header_prefix}” removed")

    # Blank scans often sit on otherwise empty pages, so classify every image once.
    removed_images = {name for name in entries if re.search(r"\.(jpe?g|png)$", name, re.IGNORECASE)
                      and is_blank_image(entries[name])}

    flagged, pages_changed, reflow_stats, page_headings = [], 0, {}, {}
    for name, (text, blob) in candidate_pages.items():
        img_tags = re.findall(r"<img\b[^>]*>", text)
        for tag in img_tags:
            src = re.search(r'src="([^"]+)"', tag)
            matches = [n for n in entries if src and n.endswith(src.group(1))]
            if matches and matches[0] not in removed_images and looks_like_page_scan(entries[matches[0]], len(blob)):
                flagged.append((name, matches[0]))

        anchor_prefix = re.sub(r"[^A-Za-z0-9]", "", posixpath.splitext(posixpath.basename(name))[0]) or "sec"
        new_body, changed, headings = reflow_page_text(blob, header_prefix, anchor_prefix, stats=reflow_stats)
        if headings:
            page_headings[name] = headings
        new_body += "".join(t for t in img_tags if not any(posixpath.basename(r) in t for r in removed_images))
        new_text = re.sub(r"(<body[^>]*>)(.*)(</body>)", lambda m, b=new_body: m.group(1) + b + m.group(3), text,
                          flags=re.DOTALL)
        if new_text != text:
            entries[name] = new_text.encode("utf-8")
            pages_changed += changed

    # Full-page scans next to their OCR text: drop pure-text duplicates, crop figures (and captions)
    # out of mixed pages, keep plates and tables whole.
    crop_stats = {"deleted": 0, "cropped": 0, "kept": 0}
    textdup_images, table_scan_pages, new_manifest_items, fig_seq = set(), set(), [], 0
    for page_name, img_name in flagged:
        if img_name not in entries:
            continue
        # A page 0/1 scan is usually the title page and may be the only cover art: keep it.
        if re.search(r"image_000[01]_", posixpath.basename(img_name)):
            crop_stats["kept"] += 1
            continue
        # Many tokens with digits or degree marks: a table. OCR flattens its columns, so the scan is
        # the only readable copy.
        tokens = candidate_pages.get(page_name, ("", ""))[1].split()
        if tokens and sum(1 for t in tokens if re.search(r"[0-9°'½¼]", t)) / len(tokens) > 0.05:
            crop_stats["kept"] += 1
            table_scan_pages.add(page_name)
            continue
        try:
            verdict, crops = crop_figures(entries[img_name])
        except (*BAD_IMAGE, ArithmeticError, IndexError):
            crop_stats["kept"] += 1
            continue
        if verdict == "TEXT_ONLY":
            textdup_images.add(img_name)
            removed_images.add(img_name)
            crop_stats["deleted"] += 1
        elif verdict == "FIGURE" and crops:
            entries[img_name] = crops[0]
            crop_stats["cropped"] += 1
            if len(crops) > 1 and page_name in entries:
                extra_tags = ""
                for extra in crops[1:]:
                    fig_seq += 1
                    new_name = re.sub(r"\.jpe?g$", "", img_name, flags=re.IGNORECASE) + f"_fig{fig_seq}.jpg"
                    entries[new_name] = extra
                    new_manifest_items.append((new_name, f"figcrop_{fig_seq}"))
                    extra_tags += f'<img src="{posixpath.basename(new_name)}" alt=""/>'
                doc = re.sub(rf'(<img\b[^>]*src="[^"]*{re.escape(posixpath.basename(img_name))}"[^>]*/?>)',
                             lambda m, t=extra_tags: m.group(1) + t, decode_text(entries[page_name]), count=1)
                entries[page_name] = doc.encode("utf-8")
        else:
            crop_stats["kept"] += 1

    # Recurring column-header "headings" go while every one of them is still counted.
    artifact_toksets = suppress_artifact_headings(entries, page_headings, notes)

    # On table pages kept as scans, the scan is the real copy and the OCR text the garbled one: keep
    # only the image(s). A run of them is usually a reference table at the back, so the first page of
    # each run gets one clean "Reference Tables" heading instead of dozens of mangled ones.
    if table_scan_pages:
        def page_num(n):
            m = re.search(r"(\d+)", posixpath.basename(n))
            return int(m.group(1)) if m else -1

        def is_artifact_fragment(t):
            # 75% overlap, not a strict subset: OCR garble ("Sfam1N") adds junk tokens.
            ts = frozenset(w for w in re.findall(r"[a-z]+", t.lower()) if len(w) >= 3)
            return ts and any(len(ts & ats) / len(ts) >= 0.75 for ats in artifact_toksets)

        ordered = sorted(table_scan_pages, key=page_num)
        run_starts = {n for i, n in enumerate(ordered)
                      if i + 2 < len(ordered) and page_num(ordered[i + 2]) - page_num(n) <= 4
                      and (i == 0 or page_num(n) - page_num(ordered[i - 1]) > 4)}
        for name in table_scan_pages:
            if name not in entries:
                continue
            doc = decode_text(entries[name])
            body = re.search(r"<body[^>]*>(.*)</body>", doc, re.DOTALL)
            if not body:
                continue
            imgs = "".join(re.findall(r"<img\b[^>]*/?>", body.group(1)))
            survivors = [(h, t) for h, t in page_headings.get(name, []) if not is_artifact_fragment(t)]
            page_headings[name] = survivors
            if not survivors:
                page_headings.pop(name, None)
            heading_html = "".join(f'<h3 id="{hid}">{html.escape(t)}</h3>' for hid, t in survivors)
            if not survivors and name in run_starts:
                hid = re.sub(r"[^A-Za-z0-9]", "", posixpath.splitext(posixpath.basename(name))[0]) + "_tbl"
                heading_html = f'<h3 id="{hid}">Reference Tables</h3>'
                page_headings[name] = [(hid, "Reference Tables")]
            entries[name] = (doc[:body.start(1)] + heading_html + imgs + doc[body.end(1):]).encode("utf-8")
        notes.append(f"{plural(len(table_scan_pages), 'table page')} kept as scans")

    if removed_images:
        alternatives = "|".join(re.escape(posixpath.basename(r)) for r in sorted(removed_images))
        for name in list(entries):
            if XHTML_EXT_RE.search(name):
                doc = decode_text(entries[name])
                new_doc = re.sub(rf'<img\b[^>]*src="[^"]*/?({alternatives})"[^>]*/?>', "", doc)
                if new_doc != doc:
                    entries[name] = new_doc.encode("utf-8")

    # Pages left with no text and no image render blank.
    empty_pages = set()
    for name in list(entries):
        if not XHTML_EXT_RE.search(name) or posixpath.basename(name) == "nav.xhtml":
            continue
        body = re.search(r"<body[^>]*>(.*)</body>", decode_text(entries[name]), re.DOTALL)
        if not body:
            continue
        kept_img = any(not any(r.endswith(posixpath.basename(m.group(1))) for r in removed_images)
                       for m in re.finditer(r'<img\b[^>]*src="([^"]+)"', body.group(1)))
        if not re.sub(r"<[^>]+>", "", body.group(1)).strip() and not kept_img:
            empty_pages.add(name)

    notice_pages = {n for n in entries if posixpath.basename(n).lower() == "notice.html"}
    drop_docs = empty_pages | notice_pages
    for gone in removed_images | drop_docs:
        entries.pop(gone, None)

    opf_name = find_opf(entries)
    if opf_name:
        opf = decode_text(entries[opf_name])
        base_dir = posixpath.dirname(opf_name)
        opf = prune_dangling_manifest_items(entries, opf, base_dir, notes, frozenset(removed_images | drop_docs))

        dropped_ids = set()
        for gone in drop_docs | removed_images:
            href = re.escape(rel_to(base_dir, gone))
            for m in re.finditer(rf'<item\b[^>]*href="{href}"[^>]*id="([^"]+)"[^>]*/>|'
                                 rf'<item\b[^>]*id="([^"]+)"[^>]*href="{href}"[^>]*/>', opf):
                dropped_ids.add(m.group(1) or m.group(2))
            opf = re.sub(rf'\s*<item\b[^>]*href="{href}"[^>]*/>', "", opf)
        for dropped in dropped_ids:
            opf = re.sub(rf'\s*<itemref\b[^>]*idref="{re.escape(dropped)}"[^>]*/>', "", opf)

        # archive.org leaves a spine entry "cover" that matches no manifest item, which some readers hang
        # on. Remove it, and wire the cover through metadata on an existing image, never the spine.
        has_cover = re.search(r'properties="[^"]*cover-image', opf) or re.search(r'<meta\s+name="cover"', opf)
        if re.search(r'<itemref\s+idref="cover"\s*/>', opf) and "cover" not in manifest_items(opf):
            opf = re.sub(r'\s*<itemref\s+idref="cover"\s*/>', "", opf)
            notes.append("dangling cover entry removed")
        if not has_cover:
            first_page = next((rel_to(base_dir, n) for n in sorted(entries)
                               if re.search(r"image_000[01]_", posixpath.basename(n))
                               and re.search(r"\.(jpe?g|png)$", n, re.IGNORECASE)), None)
            if first_page:
                item = re.search(rf'<item\b[^>]*href="{re.escape(first_page)}"[^>]*id="([^"]+)"'
                                 rf'[^>]*media-type="image/[^"]*"([^>]*)/>', opf) or \
                    re.search(rf'<item\b[^>]*id="([^"]+)"[^>]*href="{re.escape(first_page)}"'
                              rf'[^>]*media-type="image/[^"]*"([^>]*)/>', opf)
                if item:
                    item_id, old_tag = item.group(1), item.group(0)
                    if "properties=" not in old_tag:
                        opf = opf.replace(old_tag, old_tag[:-2] + ' properties="cover-image"/>', 1)
                    opf = opf.replace("</metadata>", f'  <meta name="cover" content="{item_id}"/>\n  </metadata>', 1)
                    notes.append("cover set from the first page")
            else:
                notes.append("no first-page image to use as a cover")

        for href, item_id in new_manifest_items:
            opf = opf.replace("</manifest>", f'  <item href="{rel_to(base_dir, href)}" id="{item_id}" '
                                             'media-type="image/jpeg"/>\n  </manifest>', 1)

        # The biggest win on the X4: spine-item count drives first-open indexing and page-turn stalls.
        mergeable = {n for n in candidate_pages if n in entries}
        if len(mergeable) > 3:
            opf = merge_pages_into_chapters(entries, opf, base_dir, mergeable, page_headings, notes)
        entries[opf_name] = opf.encode("utf-8")

        for name in list(entries):  # existing nav and NCX entries for dropped pages
            low = posixpath.basename(name).lower()
            if low == "nav.xhtml" or low.endswith(".ncx"):
                doc = original = decode_text(entries[name])
                for gone in drop_docs:
                    gb = re.escape(posixpath.basename(gone))
                    doc = re.sub(rf'<li>\s*<a[^>]*href="[^"]*{gb}[^"]*"[^>]*>.*?</a>\s*</li>', "", doc, flags=re.DOTALL)
                    doc = re.sub(rf"<navPoint\b[^>]*>(?:(?!</navPoint>).)*?{gb}(?:(?!</navPoint>).)*?</navPoint>", "", doc,
                                 flags=re.DOTALL)
                if doc != original:
                    entries[name] = doc.encode("utf-8")

        # These books ship an empty table of contents; build one from the detected headings.
        title = re.sub(r"\s*-\s*Unknown$", "", book_title).strip()
        nav_html, ncx_map, toc_count = build_toc(opf, base_dir, page_headings, title)
        if toc_count:
            if nav_name := next((n for n in entries if posixpath.basename(n).lower() == "nav.xhtml"), None):
                nav_doc = re.sub(r'<nav\b[^>]*epub:type="toc".*?</nav>', lambda m: nav_html, decode_text(entries[nav_name]),
                                 count=1, flags=re.DOTALL)
                entries[nav_name] = nav_doc.replace("<title></title>", f"<title>{html.escape(title)}</title>", 1).encode("utf-8")
            if ncx_name := next((n for n in entries if n.lower().endswith(".ncx")), None):
                ncx_doc = re.sub(r"<navMap\s*/>", lambda m: ncx_map, decode_text(entries[ncx_name]), count=1)
                ncx_doc = re.sub(r"<navMap\b.*?</navMap>", lambda m: ncx_map, ncx_doc, count=1, flags=re.DOTALL)
                ncx_doc = ncx_doc.replace('content="0" name="dtb:depth"', 'content="1" name="dtb:depth"')
                ncx_doc = re.sub(r"(<docTitle>\s*<text>)(</text>)", lambda m: m.group(1) + html.escape(title) + m.group(2),
                                 ncx_doc, count=1)
                entries[ncx_name] = ncx_doc.encode("utf-8")
            notes.append(f"{plural(toc_count, 'table-of-contents entry', 'table-of-contents entries')}")

    if drop_docs:
        notes.append(f"{plural(len(drop_docs), 'junk page')} removed")
    if pages_changed:
        notes.insert(0, f"{plural(pages_changed, 'page')} reflowed")
    if reflow_stats.get("noise"):
        notes.append(f"{plural(reflow_stats['noise'], 'stray OCR character')} removed")
    if reflow_stats.get("hdr"):
        notes.append(f"{plural(reflow_stats['hdr'], 'glued running header')} removed")
    if blank := len(removed_images - textdup_images):
        notes.append(f"{plural(blank, 'blank image')} removed")
    if flagged:
        notes.append(f"page scans: {crop_stats['deleted']} dropped, {crop_stats['cropped']} cropped, "
                     f"{crop_stats['kept']} kept")
    return entries, notes



# ── Checking a result ─────────────────────────────────────────────────────────
# A book is only replaced when its new version has no structural problem the original didn't have.

def structure_problems(entries: dict[str, bytes]) -> list[str]:
    """Missing files, dangling spine entries, broken images and links: what a bad edit could cause."""
    names = set(entries)
    opf_name = find_opf(entries)
    if not opf_name:
        return ["no package document (.opf)"]
    base = posixpath.dirname(opf_name)
    items, spine = package_parts(entries[opf_name])
    problems = [f"listed but missing: {a['href']}" for a in items.values()
                if posixpath.normpath(posixpath.join(base, unquote(a["href"]))) not in names]
    for idref in spine:
        if idref not in items:
            problems.append(f"reading order names a missing item: {idref}")
        elif items[idref].get("media-type", "").startswith("image/"):
            problems.append(f"an image in the reading order: {idref}")

    texts = {}

    def text_of(name):
        if name not in texts:
            texts[name] = decode_text(entries[name])
        return texts[name]

    for name in sorted(names):
        if not re.search(r"\.(xhtml|html|htm|ncx)$", name, re.IGNORECASE):
            continue
        doc, folder, short_name = text_of(name), posixpath.dirname(name), posixpath.basename(name)
        for src in re.findall(r'<img\b[^>]*src="([^"#]+)"', doc):
            if posixpath.normpath(posixpath.join(folder, unquote(html.unescape(src)))) not in names:
                problems.append(f"{short_name}: missing image {src}")
        for href, anchor in re.findall(r'(?:href|src)="([^"#]+)#([^"]+)"', doc):
            target = posixpath.normpath(posixpath.join(folder, unquote(html.unescape(href))))
            if target in names and f'id="{anchor}"' not in text_of(target):
                problems.append(f"{short_name}: link to a missing spot {href}#{anchor}")
        if short_name.lower() == "nav.xhtml" or name.lower().endswith(".ncx"):
            for ref in re.findall(r'(?:href|src)="([^"#:]+)"', doc):
                if posixpath.normpath(posixpath.join(folder, unquote(html.unescape(ref)))) not in names:
                    problems.append(f"{short_name}: contents link to a missing page {ref}")
    return problems


def new_problems(original: dict[str, bytes], data: bytes) -> list[str]:
    try:
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            damaged = archive.testzip()
            first = archive.infolist()[0].filename if archive.infolist() else ""
        result = read_epub(data)
    except BAD_ZIP:
        return ["the new file isn't a readable EPUB"]
    if damaged:
        return [f"damaged file inside: {damaged}"]
    if "mimetype" in original and first != "mimetype":
        return ["mimetype isn't first"]
    before = set(structure_problems(original))
    problems = [p for p in structure_problems(result) if p not in before]
    for name, content in result.items():
        if not re.search(r"\.(xhtml|html|htm|opf|ncx)$", name, re.IGNORECASE) or parses(content):
            continue
        if name not in original:  # a page Clean made
            problems.append(f"{posixpath.basename(name)} isn't valid XML")
        elif parses(original[name]):
            problems.append(f"{posixpath.basename(name)} is no longer valid XML")
    return problems



# ── Preparing a book: clean, then optimize, in one pass ───────────────────────

@dataclass
class Steps:
    clean: bool = True       # archive.org scans only; every other book is never cleaned
    optimize: bool = True


@dataclass
class Prepared:
    data: bytes | None = None                           # the new book; None when nothing changed or it failed

    cleaned: list[str] = field(default_factory=list)    # notes for the review
    optimized: list[str] = field(default_factory=list)
    unchanged: str = ""                                 # why nothing changed
    error: str = ""
    spine_changed: bool = False
    metadata: dict = field(default_factory=dict)

    def summary(self) -> str:
        """Every repair, for the log."""
        parts = ([f"clean: {', '.join(self.cleaned)}"] if self.cleaned else []) + \
                ([f"optimize: {', '.join(self.optimized)}"] if self.optimized else [])
        return " · ".join(parts)

    def brief(self) -> str:
        """What was done, in a word or two, for a preview: the details are in the log."""
        return ", ".join(word for word, done in (("cleaned", self.cleaned), ("optimized", self.optimized)) if done)


def drm_protected(entries: dict[str, bytes]) -> bool:
    """Whether a book is locked to a store's reading app (Adobe, Readium LCP): its pages are encrypted. Only
    fonts are ever scrambled in a book that isn't, so the X4 can read it."""
    if "META-INF/rights.xml" in entries or "META-INF/license.lcpl" in entries:
        return True
    if encryption := entries.get("META-INF/encryption.xml"):
        refs = re.findall(r'<(?:\w+:)?CipherReference\b[^>]*URI="([^"]+)"', decode_text(encryption))
        return any(not FONT_EXT_RE.search(unquote(ref)) for ref in refs)
    return False


def prepare(raw: bytes, title: str, steps: Steps, settings: OptimizeSettings, *, force: bool = False) -> Prepared:
    """One book through the steps it needs, checked before it's handed back. Never raises for a bad book."""
    try:
        entries = read_epub(raw)
    except BAD_ZIP:
        return Prepared(error="not a readable EPUB")
    if drm_protected(entries):  # its pages are ciphertext: any change would only damage them
        return Prepared(unchanged="locked with DRM, which the X4 can't read")
    result = Prepared()
    try:
        result.metadata, scan = opf_metadata(entries), looks_like_scan(entries)
        base = utf8_entries(entries)
        work, reasons = base, []
        if steps.clean:
            if scan:
                cleaned, notes = clean(base, title)
                if cleaned != base:
                    work, result.cleaned = cleaned, notes
                else:
                    reasons.append("nothing to clean")
            elif not steps.optimize:
                reasons.append("not an archive.org scan")
        if steps.optimize:
            if work is not base or force or not is_optimized(work):
                before = entries if work is base else work  # the book as it came, unless Clean changed its words
                work, result.optimized = optimize(work, settings)
                # Optimize never removes words; if a page's text changed, something went wrong.
                if lost := [posixpath.basename(n) for n in before if XHTML_EXT_RE.search(n) and n in work
                            and visible_text(decode_text(before[n])) != visible_text(decode_text(work[n]))]:
                    result.error = f"optimizing changed the text of {', '.join(lost[:3])}; left as it was"
                    result.cleaned, result.optimized = [], []
                    return result
            else:
                reasons.append("already optimized")
    except Exception as error:  # noqa: BLE001 - one odd book mustn't stop the rest; it's left as it was
        result.error = f"couldn't be processed ({type(error).__name__}: {error})"
        return result

    if work == base:
        result.unchanged = ", ".join(reasons) or "nothing to change"
        result.cleaned, result.optimized = [], []
        return result
    try:
        data = pack_epub(work)
        problems = new_problems(entries, data)
        spine_changed = spine_paths(entries) != spine_paths(work)
    except Exception as error:  # noqa: BLE001 - as above: this book is left as it was, the rest carry on
        result.error = f"couldn't be checked ({type(error).__name__}: {error})"
        return result
    if problems:
        result.error = "the result failed its check: " + "; ".join(problems[:3]) + \
            (f" (+{len(problems) - 3} more)" if len(problems) > 3 else "")
        return result
    result.data, result.spine_changed = data, spine_changed
    return result



# ── Names on the card ─────────────────────────────────────────────────────────
# [ Genre ]/Last, First/Title, The.epub: author from the book's file-as name, title from its sort
# title, ':' as ' - ', no '?', no trailing dot. One author per book: the first real author.

NAME_SUFFIXES = {"jr", "jr.", "sr", "sr.", "ii", "iii", "iv"}
AUTHOR_ROLES = {"", "aut"}


def _cp437_repairs() -> dict[str, str]:
    """Accented letters from zip file names stored in the old DOS code page (CP437) come out as
    punctuation when read as Windows-1252 or Shift-JIS: é as ‚, ö as ”, ú as ｣. Maps them back."""
    table = {}
    for byte in range(0x80, 0x100):
        letter = bytes([byte]).decode("cp437")
        if not letter.isalpha():
            continue
        for codec in ("cp1252", "cp932"):
            try:
                shown = bytes([byte]).decode(codec)
            except UnicodeDecodeError:
                continue
            if len(shown) == 1 and not shown.isalpha() and shown not in "‘’–—":
                table.setdefault(shown, letter)
    return table


CP437_REPAIRS = _cp437_repairs()


def repair_garbled(text: str, *, from_file_name: bool) -> str:
    """Undo mangled characters. UTF-8 read as Windows-1252 ("CafÃ©") is fixed when the whole name
    decodes cleanly. The CP437 kind is only fixed in file names, between two letters ("H｣rin")."""
    if re.search(r"[ÃÂâ]", text):
        try:
            text = text.encode("cp1252").decode("utf-8")
        except UnicodeError:
            pass
    if from_file_name:
        chars = list(text)
        for i in range(1, len(chars) - 1):
            if chars[i] in CP437_REPAIRS and chars[i - 1].isalpha() and chars[i + 1].isalpha():
                chars[i] = CP437_REPAIRS[chars[i]]
        text = "".join(chars)
    return nfc(text)


def card_name(text: str) -> str:
    """A title or author as a name the card can hold, never hidden (a leading dot); "" if nothing is left."""
    text = nfc(text).replace("\u00a0", " ")
    text = re.sub(r"\s*:\s*", " - ", text)
    text = re.sub(r"\s*[/\\|]\s*", " - ", text)
    text = re.sub(r'[?*<>\x00-\x1f]', "", text).replace('"', "'")
    text = re.sub(r"\s+", " ", text).strip()
    return text.strip(". ,").strip()


def sort_title(metadata: dict, fallback: str) -> str:
    """The sort title ("Prince, The"), or the title with its leading article moved to the end; the
    file's own name when the book has neither."""
    title = metadata.get("title_sort") or ""
    if not title and (title := metadata.get("title") or "") and \
            (m := re.match(r"^(The|A|An)\s+(.+)$", title, re.IGNORECASE)):
        title = f"{m.group(2)}, {m.group(1).capitalize()}"
    title = (card_name(repair_garbled(title, from_file_name=False)) if title else "") \
        or card_name(repair_garbled(fallback, from_file_name=True)) or "Untitled"
    title = shorten(title, 180)
    return title[:1].upper() + title[1:]


def shorten(text: str, limit: int) -> str:
    return text if len(text) <= limit else text[:limit].rsplit(" ", 1)[0].rstrip(" ,-") + "…"


def author_folder(metadata: dict) -> str:
    """"Last, First" for the book's first real author (not an editor or translator), or ""."""
    authors = [a for a in metadata.get("authors", []) if a["role"] in AUTHOR_ROLES and (a["name"] or a["file_as"])]
    if not authors:
        return ""
    name = repair_garbled(authors[0]["file_as"] or authors[0]["name"], from_file_name=False)
    name = re.split(r"\s*(?:;|&|\band\b)\s*", name)[0]                             # the first of several
    name = re.sub(r"\(.*?\)|,?\s*\d{3,4}\s*-\s*(?:\d{3,4})?\s*$", "", name).strip(" ,")  # (roles), life dates
    suffix = re.search(r",?\s+(jr|sr|ii|iii|iv)\.?$", name, re.IGNORECASE)
    if suffix:
        name = name[:suffix.start()]
    if "," not in name and len(words := name.split()) > 1:                     # "First Last" -> "Last, First"
        name = f"{words[-1]}, {' '.join(words[:-1])}"
    if suffix:
        name += f" {suffix.group(1)}"
    return shorten(card_name(name), 120)


def fold(name: str) -> str:
    """For matching names loosely: accents, case and stray spaces ignored."""
    decomposed = unicodedata.normalize("NFKD", name)
    return re.sub(r"\s+", " ", "".join(c for c in decomposed if not unicodedata.combining(c))).casefold().strip(" .")


def place_book(root: Path, genre: str, metadata: dict, fallback: str) -> str:
    """Where a new book goes, reusing an author folder that's already in the genre."""
    author = author_folder(metadata)
    if author:
        existing = [e.name for e in visible_entries(root, genre) if e.is_dir() and fold(e.name) == fold(author)]
        author = existing[0] if existing else author
    file_name = sort_title(metadata, fallback) + ".epub"
    return "/".join(part for part in (genre, author, file_name) if part)



# ── Finding cards ─────────────────────────────────────────────────────────────

@dataclass
class Card:
    name: str
    mount: Path
    device: str       # e.g. /dev/disk5s1
    whole: str        # the whole disk, for eject, e.g. /dev/disk5
    fs: str           # fat32, exfat, apfs, …
    fs_label: str     # FAT32, exFAT, APFS, …
    size: int
    free: int
    kind: str         # "SD card · USB reader", "disk image", …
    uuid: str
    writable: bool

    @property
    def is_x4(self) -> bool:
        return (self.mount / DEVICE_DIR).is_dir()

    def problem(self, *, changes: bool = True) -> str | None:
        """Why the tool can't use this card, if it can't. A task that only reads (Check) can use any card."""
        if off_limits(self.mount):
            return f"mounted at {self.mount}; give it its own folder"
        if not changes:
            return None
        if self.fs not in FAT_FAMILY:
            return f"the X4 can't read {self.fs_label}"
        if not self.writable:
            return "read-only: check the card's lock switch"
        if not self.uuid:  # every write checks the card by its ID first, so none could go ahead
            return "no volume ID, so writes can't be checked to land on this card"
        return None


def list_cards() -> list[Card]:
    """Every mounted removable or external volume. The computer's own drives never appear."""
    return _mac_cards() if IS_MAC else _linux_cards()


def diskutil_info(target: str) -> dict:
    result = run(["diskutil", "info", "-plist", target], timeout=30, detail=True) if target else None
    if result is None or result.returncode != 0:
        return {}
    try:
        return plistlib.loads(result.stdout.encode())
    except (ValueError, xml.parsers.expat.ExpatError):
        return {}


def _removable(info: dict) -> bool:
    return bool(info.get("Removable") or info.get("RemovableMedia") or info.get("Ejectable"))


def _mac_cards() -> list[Card]:
    cards = []
    try:
        entries = sorted(Path("/Volumes").iterdir())
    except OSError:
        return cards
    for entry in entries:
        if entry.is_symlink() or not os.path.ismount(entry):
            continue
        volume = diskutil_info(str(entry))
        whole = volume.get("ParentWholeDisk", "")
        if card := mac_card_from_info(volume, diskutil_info(whole)):
            cards.append(card)
    return cards


def mac_card_from_info(volume: dict, disk: dict, usage=shutil.disk_usage) -> Card | None:
    mount = volume.get("MountPoint") or ""
    if mount in ("", "/"):
        return None
    if volume.get("Internal") and not (_removable(volume) or _removable(disk)):
        return None  # the Mac's own drive
    try:
        space = usage(mount)
    except OSError:
        return None

    kind_of = (volume.get("FilesystemType") or "").lower()
    name = volume.get("FilesystemName") or volume.get("FilesystemUserVisibleName") or kind_of
    if kind_of == "exfat":
        fs, fs_label = "exfat", "exFAT"
    elif kind_of == "msdos":
        bits = found.group(1) if (found := re.search(r"FAT(12|16|32)", name)) else "32"
        fs, fs_label = f"fat{bits}", f"FAT{bits}"
    else:
        fs, fs_label = kind_of or "unknown", name or "an unknown format"

    bus = disk.get("BusProtocol") or volume.get("BusProtocol") or ""
    media = f"{disk.get('MediaName', '')} {disk.get('IORegistryEntryName', '')}"
    if bus == "Disk Image":
        kind = "disk image"
    elif bus == "Secure Digital":
        kind = "SD card · built-in reader"
    elif SD_HINT.search(media):
        kind = f"SD card · {bus or 'USB'} reader"
    elif bus == "USB" and fs in FAT_FAMILY:
        kind = "card or USB stick"  # plenty of readers name only their chip, e.g. "NORELSYS 1081CS0"
    else:
        kind = f"{bus} drive" if bus else "drive"

    whole = volume.get("ParentWholeDisk")
    return Card(
        name=volume.get("VolumeName") or Path(mount).name,
        mount=Path(mount),
        device=volume.get("DeviceNode", ""),
        whole=f"/dev/{whole}" if whole else volume.get("DeviceNode", ""),
        fs=fs, fs_label=fs_label,
        size=space.total, free=space.free,
        kind=kind,
        uuid=volume.get("VolumeUUID") or volume.get("DiskUUID") or "",
        writable=bool(volume.get("WritableVolume", True)),
    )


def _truthy(value) -> bool:
    return value in (True, 1, "1", "true")


def _linux_cards() -> list[Card]:
    columns = "NAME,PATH,PKNAME,TYPE,RM,HOTPLUG,TRAN,VENDOR,MODEL,LABEL,FSTYPE,FSVER,MOUNTPOINT,UUID,RO"
    result = run(["lsblk", "--json", "--bytes", "--list", "-o", columns], detail=True)
    if result.returncode != 0:
        return []
    try:
        return linux_cards_from_lsblk(json.loads(result.stdout), mount_types=_mount_types(), probe_uuid=_probe_uuid,
                                      mmc_type=_mmc_type)
    except ValueError:
        return []


def _mount_types() -> dict[str, str]:
    """Mount point to filesystem type, from the kernel's own table (lsblk needs udev for this)."""
    types = {}
    try:
        for line in Path("/proc/self/mounts").read_text().splitlines():
            _, mount, fs_type = line.split()[:3]
            types[re.sub(r"\\([0-7]{3})", lambda m: chr(int(m.group(1), 8)), mount)] = fs_type
    except (OSError, ValueError):
        pass
    return types


def _probe_uuid(device: str) -> str:
    """Read the ID from the device itself (-p skips blkid's cache, which can be stale)."""
    if not shutil.which("blkid"):
        return ""
    return run(["blkid", "-p", "-s", "UUID", "-o", "value", device], detail=True).stdout.strip()


def _mmc_type(name: str) -> str:
    """'SD' for a card in a slot, 'MMC' for built-in eMMC storage."""
    try:
        return Path(f"/sys/block/{name}/device/type").read_text().strip()
    except OSError:
        return ""


def linux_cards_from_lsblk(data: dict, usage=shutil.disk_usage, mount_types: dict | None = None,
                           probe_uuid=lambda device: "", mmc_type=lambda name: "") -> list[Card]:
    rows = data.get("blockdevices", [])
    by_name = {row.get("name"): row for row in rows}
    cards = []
    for row in rows:
        mount = row.get("mountpoint")
        if not mount or mount in ("/", "[SWAP]") or mount.startswith(("/boot", "/snap", "/efi")):
            continue
        parent = by_name.get(row.get("pkname")) or row
        loop = "loop" in (row.get("type"), parent.get("type"))

        kind_of = (row.get("fstype") or (mount_types or {}).get(mount) or "").lower()
        if kind_of == "exfat":
            fs, fs_label = "exfat", "exFAT"
        elif kind_of in ("vfat", "msdos", "fat"):
            bits = re.search(r"(12|16|32)", row.get("fsver") or "")
            fs, fs_label = (f"fat{bits.group(1)}", f"FAT{bits.group(1)}") if bits else ("fat", "FAT")
        else:
            fs, fs_label = kind_of or "unknown", kind_of or "an unknown format"

        # mmcblk is also built-in eMMC storage; the kernel says "SD" only for a card in a slot.
        parent_name = str(parent.get("name", ""))
        sd_slot = parent_name.startswith("mmcblk") and mmc_type(parent_name) == "SD"
        removable = loop or sd_slot or any(_truthy(source.get(key)) for source in (row, parent) for key in ("rm", "hotplug"))
        if not removable or (loop and fs not in FAT_FAMILY):
            continue  # internal drives, and loop mounts that are really snaps
        try:
            space = usage(mount)
        except OSError:
            continue

        transport = parent.get("tran") or ""
        label = f"{parent.get('vendor') or ''} {parent.get('model') or ''}"
        if loop:
            kind = "disk image"
        elif sd_slot:
            kind = "SD card · built-in reader"
        elif SD_HINT.search(label):
            kind = "SD card · USB reader"
        elif transport == "usb" and fs in FAT_FAMILY:
            kind = "card or USB stick"
        else:
            kind = f"{transport.upper()} drive" if transport else "drive"

        device = row.get("path") or f"/dev/{row.get('name')}"
        cards.append(Card(
            name=row.get("label") or Path(mount).name,
            mount=Path(mount),
            device=device,
            whole=parent.get("path") or f"/dev/{parent.get('name')}",
            fs=fs, fs_label=fs_label,
            size=space.total, free=space.free,
            kind=kind,
            uuid=row.get("uuid") or probe_uuid(device),
            writable=not _truthy(row.get("ro")),
        ))
    return cards


def device_still_matches(card: Card) -> bool:
    """Is the device still the card the user picked? Checked by its ID right before anything writes."""
    if not card.uuid:
        return False
    if IS_MAC:
        info = diskutil_info(card.device)
        removable = _removable(info) or not info.get("Internal")
        return bool(info) and removable and (info.get("VolumeUUID") or info.get("DiskUUID")) == card.uuid
    found = run(["lsblk", "-no", "UUID", card.device], detail=True).stdout.strip() or _probe_uuid(card.device)
    return found == card.uuid


def card_still_here(card: Card) -> bool:
    """Is the card's folder still mounted from the same device, with the same ID?"""
    root = card.mount
    if not os.path.ismount(root) or off_limits(root):
        return False
    if IS_MAC:
        return diskutil_info(str(root)).get("DeviceNode") == card.device and device_still_matches(card)
    try:
        mounted_from_device = os.stat(root).st_dev == os.stat(card.device).st_rdev
    except OSError:
        return False
    return mounted_from_device and device_still_matches(card)


def assert_card(card: Card) -> None:
    """Before every write to the card: still mounted, same device, same ID. Otherwise stop."""
    if not card_still_here(card):
        raise SafetyError(f"{card.mount} is no longer the card you picked ({card.name}).")


def _under(child: Path, parent: Path) -> bool:
    """child is parent or inside it; without case on macOS, where /volumes is /Volumes."""
    c, p = str(child.resolve()), str(parent.resolve()).rstrip("/")
    if IS_MAC:
        c, p = c.casefold(), p.casefold()
    return c == p or c.startswith(p + "/")


def off_limits(path: Path) -> bool:
    """/, /Volumes, the home folder and the like: never a source or target in their own right."""
    return any(_under(path, p) and _under(p, path) for p in NEVER_TOUCH)


def card_for(path: Path) -> Card | None:
    """The card a path is on, found by device, so a path typed in another case still counts."""
    try:
        device = os.stat(path).st_dev
    except OSError:
        return None
    for card in list_cards():
        try:
            if os.stat(card.mount).st_dev == device:
                return card
        except OSError:
            continue
    return None


def card_device_ids() -> set[int]:
    ids = set()
    for card in list_cards():
        try:
            ids.add(os.stat(card.mount).st_dev)
        except OSError:
            pass
    return ids


def path_arg(opts: Options) -> Path | None:
    """The path given on the command line, checked the same way for every task."""
    if not opts.path:
        return None
    path = clean_path(opts.path)
    if not path.exists():
        raise SafetyError(f"Can't find {tilde(path)}.")
    return path


def usable_card_for(path: Path) -> Card | None:
    """The card a path is on, refused when the card list would grey it out."""
    card = card_for(path)
    if card and (problem := card.problem()):
        raise SafetyError(f"{card.name}: {problem}.")
    return card


def card_item_arg(opts: Options) -> tuple[Card, str] | None:
    """For Move and Remove: the book or folder on the card given on the command line."""
    if (path := path_arg(opts)) is None:
        return None
    if (card := usable_card_for(path)) is None:
        raise SafetyError(f"{tilde(path)} isn't on a card.")
    rel = card_rel(card, path)
    if not rel:
        raise SafetyError("That's the whole card. Give a book or a folder on it.")
    if system_path(rel):
        raise SafetyError(SYSTEM_FOLDER)
    if not path.is_dir() and posixpath.splitext(rel)[1].lower() not in RECORD_PREFIXES:
        raise SafetyError(f"{rel} isn't a folder or a book.")
    return card, rel


def with_extension(raw: str, old_name: str, is_dir: bool) -> str:
    """A typed new name. A book keeps its own extension (.epub, .txt, …); a trailing dot goes."""
    name = raw.strip().rstrip(". ")
    ext = "" if is_dir else posixpath.splitext(old_name)[1]
    return name if not ext or name.lower().endswith(ext.lower()) else name + ext


def locate(target: Path, *, backups_ok: bool = False, changes: bool = True) -> tuple[Card | None, Path, str]:
    """For a folder or book: the card it's on (if any), the root its paths count from, and its path
    from there ("" for all of it). A folder on this computer goes through check_local first. When the
    task `changes` books, a card the card list would grey out is refused."""
    if card := (usable_card_for(target) if changes else card_for(target)):
        if system_path(rel := card_rel(card, target)) and rel:
            raise SafetyError(SYSTEM_FOLDER)
        return card, card.mount, rel
    check_local(target, backups_ok=backups_ok)
    return None, (target if target.is_dir() else target.parent), ("" if target.is_dir() else target.name)


def card_rel(card: Card, path: Path) -> str:
    """A path on the card as a card path, spelled as the card lists it ("" for the whole card)."""
    rel = str(path.resolve())[len(str(card.mount.resolve())):].strip("/")
    return (resolve_on_card(card.mount, rel) or rel) if rel else ""


def check_local(path: Path, *, backups_ok: bool = False) -> None:
    """A folder or book on this computer that the tool may read or change."""
    if off_limits(path):
        raise SafetyError(f"{tilde(path)} is too broad. Pick a folder of books.")
    for card in list_cards():
        if _under(card.mount, path):
            raise SafetyError(f"{tilde(path)} holds the card {card.name}. Pick the card, or a folder on it.")
    if not backups_ok and _under(path, RUN.backups):
        raise SafetyError("That's in the backups folder. Use Restore to put books back from there.")


def show_card(card: Card, state: dict, *, chosen: bool = False) -> int:
    """The card's box: size, books, folders. Returns how many books it has. `chosen`: it was given on the
    command line, so it needs no confirming, and from here on it's shown above each question."""
    books = list_books(card.mount)
    if chosen:
        RUN.active = (card, len(books))
        RUN.used[card_key(card)] = card
    folders = top_folders(books)
    lines = [Text(f"{human(card.size)} {card.kind} · {card.fs_label} · {human(card.free)} free"),
             Text(f"{plural(len(books), 'book')} in {plural(len(folders), 'folder')}")]
    if folders:
        lines.append(Text(", ".join(folders[:3]) + (f" … +{len(folders) - 3} more" if len(folders) > 3 else "")))
    with suppress(TypeError, ValueError):  # a hand-edited date is just not shown
        updated = datetime.fromisoformat(state.get("cards", {}).get(card.uuid, {}).get("updated"))
        lines.append(Text(f"Last changed from this computer: {updated.astimezone().date().isoformat()}",
                          style="hint"))
    boxed(lines)
    if not card.is_x4:
        warn(f"No {DEVICE_DIR} folder: this card hasn't been in an X4 running CrossPoint yet, or it isn't the "
             "X4's card.")
    return len(books)


def rank_cards(cards: list[Card], last_uuid: str | None) -> list[Card]:
    """Usable first, then X4 cards, then the card used last time, with disk images last."""
    return sorted(cards, key=lambda c: (c.problem() is not None, not c.is_x4, c.uuid != last_uuid,
                                        c.kind == "disk image", c.name.casefold()))


def choose_card(state: dict, *, changes: bool = True) -> Card | None:
    """The X4's card: picked from a list unless it's the only one, then confirmed. Once confirmed, later
    tasks in the same run use it without asking, as long as the same drives are plugged in and it isn't
    ejected. A task that only reads (`changes` False) can pick a card the others grey out."""
    while True:
        cards = rank_cards(list_cards(), state.get("card_uuid"))
        if card := still_confirmed(cards, changes=changes):
            say(f"[hint]Using {esc(card.name)}, confirmed earlier.[/]")
            RUN.used[card_key(card)] = card
            return card
        usable = [c for c in cards if c.problem(changes=changes) is None and c.is_x4]
        if not cards:
            warn("No SD card found. Insert the X4's card, then pick Rescan.")
            if ask_select("No card", [action_choice("Rescan", "rescan", "↻"), back()]) is BACK:
                return None
            continue
        if len(usable) == 1 and len(cards) == 1:
            picked = usable[0]
        else:
            width, last = max(len(c.name) for c in cards), state.get("card_uuid")
            choices = [option(c.name, c, f"{human(c.size)} {c.kind} · {c.fs_label}"
                              + ("" if c.is_x4 else " · not used in an X4 yet")
                              + ("   last used" if c.uuid and c.uuid == last else ""), width=width,
                              disabled=c.problem(changes=changes), description=f"{c.device} · {human(c.free)} free")
                       for c in cards]
            choices += [divider(), action_choice("Rescan", "rescan", "↻"), back()]
            first_ok = cards[0].problem(changes=changes) is None
            picked = ask_select("Which card?", choices, default=cards[0] if first_ok else "rescan")
            if picked is BACK:
                return None
            if picked == "rescan":
                continue
        books = show_card(picked, state)
        right = ask_confirm("Is this the right card?", True, on_escape=BACK)
        if right is BACK:
            return None
        if right:
            RUN.confirmed = (picked.uuid, frozenset(c.uuid for c in cards)) if picked.uuid else None
            RUN.active = (picked, books)
            RUN.used[card_key(picked)] = picked
            return picked
        if len(cards) == 1:
            warn("No other card found. Insert the right card, then pick Rescan.")
            if ask_select("No card", [action_choice("Rescan", "rescan", "↻"), back()]) is BACK:
                return None
        say()



def still_confirmed(cards: list[Card], *, changes: bool = True) -> Card | None:
    """The card confirmed earlier this run, if it and only the drives there then are still plugged in."""
    if RUN.confirmed is None or frozenset(c.uuid for c in cards) != RUN.confirmed[1]:
        return None
    card = next((c for c in cards if c.uuid == RUN.confirmed[0]), None)
    return card if card and card.problem(changes=changes) is None else None



# ── The X4's own records ──────────────────────────────────────────────────────
# The firmware keeps each book's cache and reading progress in /.crosspoint/epub_<N>, where N is
# libstdc++'s std::hash of the book's path (32-bit MurmurHash2), and its bookmarks in
# /.crosspoint/bookmarks/<path with / as _>.json. recent.json and state.json name books by path too.
# It never notices a replaced file, so a book changed in place shows a stale index until its cache
# goes. Everything here follows the firmware's own rename (1.6.5, FileBrowserActivity.cpp).
#
# Names: macOS's FAT driver stores names composed (NFC) on the card but lists them decomposed (NFD);
# Linux stores and lists them as given. The X4 hashes the stored bytes, so every path the X4 sees goes
# through device_path(), which spells it as stored.
# (Verified 2026-10-08 by reading a FAT32 image's raw directory entries.)

# The book types the firmware keeps records for, and its cache folder prefix for each.
RECORD_PREFIXES = {".epub": "epub_", ".xtc": "xtc_", ".xtch": "xtc_", ".txt": "txt_", ".md": "txt_"}
OTHER_KINDS = tuple(kind for kind in RECORD_PREFIXES if kind != ".epub")  # what else it opens; a "book" is an EPUB


def classify(rel: str) -> str:
    """What a path on the card is, for Back up and Restore: "book" (an EPUB), "other" (another file the X4 opens,
    sleep-screen pictures among them), "record" (the X4's own records) or "" (anything else). Only books are counted
    as books."""
    if rel.startswith(DEVICE_DIR + "/"):
        return "record"
    if is_sleep_image(rel):
        return "other"
    if system_path(rel):
        return ""
    kind = posixpath.splitext(rel)[1].lower()
    return "book" if kind == ".epub" else "other" if kind in OTHER_KINDS else ""


def is_sleep_image(rel: str) -> bool:
    """A sleep-screen picture the X4 shows: one at the card's root under its own name, or a BMP or PNG directly in
    one of its sleep folders."""
    parts = rel.split("/")
    if len(parts) == 1:
        return rel.casefold() in SLEEP_FILES
    return (len(parts) == 2 and parts[0].casefold() in SLEEP_DIRS and not parts[1].startswith(".")
            and posixpath.splitext(parts[1])[1].lower() in (".bmp", ".png"))


def sleep_images(root: Path, *, strict: bool = False) -> list[str]:
    """The sleep-screen pictures under root, as paths on the card, exactly as listed. `strict` stops on a sleep
    folder that can't be read, as list_books does."""
    found = []
    try:
        for entry in sorted(os.scandir(root), key=lambda e: natural_key(e.name)):
            if entry.is_file() and is_sleep_image(entry.name):
                found.append(entry.name)
            elif entry.is_dir(follow_symlinks=False) and entry.name.casefold() in SLEEP_DIRS:
                found += [f"{entry.name}/{inner.name}" for inner in sorted(os.scandir(entry.path),
                                                                           key=lambda e: natural_key(e.name))
                          if inner.is_file() and is_sleep_image(f"{entry.name}/{inner.name}")]
    except OSError as error:
        if strict:
            raise SafetyError(f"Couldn't read {error.filename}; nothing was changed.") from error
    return found


def stored(rel: str) -> str:
    """A path as the card holds it: composed on macOS, which writes names that way whatever it lists; on Linux,
    exactly as listed."""
    return nfc(rel) if IS_MAC else rel


def device_path(rel: str) -> str:
    """A card path as the X4 itself sees it: a leading slash, spelled as stored."""
    return "/" + stored(rel)


def path_hash(device_path: str) -> int:
    """std::hash<std::string> on the X4's 32-bit chip: MurmurHash2, seed 0xc70f6907."""
    data, m = device_path.encode("utf-8", "surrogateescape"), 0x5BD1E995  # a name Linux couldn't read: its bytes
    h = (0xC70F6907 ^ len(data)) & 0xFFFFFFFF
    whole = len(data) - len(data) % 4
    for i in range(0, whole, 4):
        k = (int.from_bytes(data[i:i + 4], "little") * m) & 0xFFFFFFFF
        k = ((k ^ (k >> 24)) * m) & 0xFFFFFFFF
        h = ((h * m) & 0xFFFFFFFF) ^ k
    tail = data[whole:]
    if len(tail) == 3:
        h ^= tail[2] << 16
    if len(tail) >= 2:
        h ^= tail[1] << 8
    if tail:
        h = ((h ^ tail[0]) * m) & 0xFFFFFFFF
    h = ((h ^ (h >> 13)) * m) & 0xFFFFFFFF
    return h ^ (h >> 15)


def _cache_at(root: Path, spelled: str) -> Path:
    prefix = RECORD_PREFIXES.get(posixpath.splitext(spelled)[1].lower(), "epub_")
    return root / DEVICE_DIR / f"{prefix}{path_hash('/' + spelled)}"


def _bookmark_at(root: Path, spelled: str) -> Path:
    """The firmware's BookmarkUtil::getBookmarkPath: slashes become underscores, the extension goes."""
    flat = spelled.replace("/", "_").replace("\\", "_")
    stem = flat[:flat.rfind(".")] if "." in flat else flat
    return root / DEVICE_DIR / "bookmarks" / f"{stem}.json"


def cache_dir(root: Path, rel: str) -> Path:
    """Where the X4 keeps a book's cache and progress, once its name is written."""
    return _cache_at(root, stored(rel))


def bookmark_file(root: Path, rel: str) -> Path:
    return _bookmark_at(root, stored(rel))


def _counterpart(record: Path, root: Path, rel: str) -> Path:
    """For one of a book's records, the same kind of record at another path."""
    return cache_dir(root, rel) if record.parent == root / DEVICE_DIR else bookmark_file(root, rel)


def existing_records(root: Path, rel: str) -> list[Path]:
    """A book's cache folder and bookmark file as they are now. The X4 may have recorded the name
    decomposed (some uploads store it that way), so both spellings are looked for."""
    if posixpath.splitext(rel)[1].lower() not in RECORD_PREFIXES:
        return []
    found, seen = [], set()
    for spelled in dict.fromkeys((stored(rel), nfc(rel), unicodedata.normalize("NFD", rel))):
        for record in (_cache_at(root, spelled), _bookmark_at(root, spelled)):
            try:
                identity = (info := os.stat(record)).st_dev, info.st_ino  # FAT finds one file by either spelling
            except OSError:
                continue
            if identity not in seen:
                seen.add(identity)
                found.append(record)
    return found


class DeviceRecords:
    """recent.json and state.json, edited in memory and saved after each change, in the firmware's compact
    format. Each save is flushed to the card, then swapped in."""

    def __init__(self, root: Path):
        self.root = root
        self.recent = self._load("recent.json")
        self.state = self._load("state.json")
        self.changed = set()

    def _load(self, name: str) -> dict | None:
        try:
            return json.loads((self.root / DEVICE_DIR / name).read_text(encoding="utf-8"))
        except (OSError, ValueError):
            return None

    def recent_books(self) -> list[dict]:
        """The recent list's entries that name a book; anything else in it is left as it is."""
        books = self.recent.get("books") if isinstance(self.recent, dict) else None
        return [b for b in books if isinstance(b, dict) and isinstance(b.get("path"), str)] \
            if isinstance(books, list) else []

    def _open_book(self) -> str:
        path = self.state.get("openEpubPath") if isinstance(self.state, dict) else None
        return path if isinstance(path, str) else ""

    def move(self, old_rel: str, new_rel: str) -> None:
        """A book or folder moved: every path at or under old_rel follows."""
        def moved(path: str) -> str | None:
            same, old = nfc(path), nfc(device_path(old_rel))  # either spelling of a name is the same name
            if same == old:
                return device_path(new_rel)
            if same.startswith(old + "/"):  # inside a moved folder: the rest stays as the card holds it
                return device_path(new_rel) + "/" + "/".join(path.split("/")[old.count("/") + 1:])
            return None

        for book in self.recent_books():
            new = moved(book["path"])
            if new and new != book["path"]:
                book["path"] = new
                if "coverBmpPath" in book:
                    book["coverBmpPath"] = re.sub(r"/(epub_|xtc_|txt_)\d+/", lambda m, n=new: f"/{m.group(1)}{path_hash(n)}/",
                                                  book["coverBmpPath"])
                self.changed.add("recent.json")
        if (new := moved(self._open_book())) and new != self._open_book():
            self.state["openEpubPath"] = new
            self.changed.add("state.json")

    def forget(self, rel: str) -> None:
        """A book removed from the card: off the recent list, and no longer the open book."""
        gone = [b for b in self.recent_books() if nfc(b["path"]) == nfc(device_path(rel))]
        if gone:
            self.recent["books"] = [b for b in self.recent["books"] if not any(b is g for g in gone)]
            self.changed.add("recent.json")
        if self._open_book() and nfc(self._open_book()) == nfc(device_path(rel)):
            self.state["openEpubPath"] = ""
            self.changed.add("state.json")

    def save(self) -> None:
        for name in sorted(self.changed):
            data = self.recent if name == "recent.json" else self.state
            target = self.root / DEVICE_DIR / name
            temp = target.with_name(f".{name}.part")
            with open(temp, "w", encoding="utf-8") as out:
                json.dump(data, out, ensure_ascii=False, separators=(",", ":"))
                out.flush()
                os.fsync(out.fileno())
            os.replace(temp, target)
        self.changed.clear()


def on_card(path: Path) -> Path:
    """A path as macOS's FAT driver can act on it. It lists accented names decomposed, yet can't
    rename a file spelled that way, nor a file created under that spelling; composed always works.
    Linux keeps names as given, so paths stay as they are there. (Tested 2026-10-08 on FAT32 images.)"""
    return Path(nfc(str(path))) if IS_MAC else path


def _clear_flags(path: Path) -> None:
    """macOS shows FAT's read-only mark (often left by Windows) as a lock, which stops a replace, rename or delete.
    It's cleared first: for a folder, everything in it too."""
    if not IS_MAC:
        return
    with suppress(OSError):
        if not path.is_dir() and not os.lstat(path).st_flags & stat.UF_IMMUTABLE:
            return  # the usual case, without running chflags for every book
    run(["chflags", "-R", "nouchg", str(path)])


def card_rename(source: Path, target: Path) -> None:
    LOG.info("   rename %s → %s", source, target)
    os.replace(on_card(source), on_card(target))


def _remove_path(path: Path) -> None:
    LOG.debug("   remove %s", path)  # an X4 record: one book can have dozens
    if path.is_dir():
        shutil.rmtree(path)
    else:
        path.unlink(missing_ok=True)


def _move_aside(source: Path, target: Path) -> bool:
    """Move a cache folder or bookmark file. A leftover at the target belongs to no book and goes;
    the same file under another spelling (case, accents) moves through a temporary name instead."""
    if source == target or not source.exists():
        return False
    on_card(target.parent).mkdir(parents=True, exist_ok=True)
    if target.exists():
        if os.path.samefile(source, target):
            temp = source.with_name(f".{source.name}.moving")
            card_rename(source, temp)
            card_rename(temp, target)
            return True
        _remove_path(target)
    card_rename(source, target)
    return True



def reset_book_records(root: Path, rel: str, *, keep_progress: bool) -> None:
    """After a book is replaced: its stale index goes. Progress and bookmarks stay when the reading
    order is the same, moved to where the X4 will look now that macOS has written the name; when the
    order changed, the saved page points nowhere, so the book starts over. An older copy under the
    other spelling of the name goes rather than overwrite the current one."""
    for record in existing_records(root, rel):
        target = _counterpart(record, root, rel)
        if not keep_progress or (record != target and target.exists() and not os.path.samefile(record, target)):
            _remove_path(record)
            continue
        if record.is_dir():
            for entry in record.iterdir():
                if entry.name != "progress.bin":
                    _remove_path(entry)
        _move_aside(record, target)


def forget_book_records(root: Path, records: DeviceRecords, rel: str) -> None:
    for record in existing_records(root, rel):
        _remove_path(record)
    records.forget(rel)



# ── Backups ───────────────────────────────────────────────────────────────────
# xteink-backups/<date>/<card or folder name>/<path>: originals. A different book at the same path later that
# day goes into "<name> (2)", so no version is lost; .source.json says where each set came from.
# xteink-backups/<date>/<card or folder name>/.device-<time>/: the X4's records before each run's changes.

def backup_day() -> Path:
    """Today's backups folder: the day the task under way started, so a task running past midnight keeps
    its backups together."""
    return RUN.backups / (RUN.day or today())


def backup_home(label: str) -> Path:
    return backup_day() / label


def backups_from(state: dict) -> Path:
    """The folder picked at "Save the backup where?", or the default beside the script."""
    return Path(state["backups"]) if state.get("backups") else DEFAULT_BACKUPS


def folder_problem(path: Path) -> str | None:
    """Why backups can't go into `path`, or None. A folder that isn't there yet is made, but only inside one
    that is: a path on a drive that isn't plugged in is refused, never made on this computer instead."""
    parts = path.parts
    if IS_MAC and len(parts) > 2 and parts[1] == "Volumes" and not Path("/Volumes", parts[2]).is_dir():
        return f"{parts[2]} isn't plugged in"
    if path.exists() and not path.is_dir():
        return "that's a file"
    home = path if path.is_dir() else path.parent
    if not home.is_dir():
        return f"{tilde(home)} isn't there"
    return None if os.access(home, os.W_OK) else f"{tilde(home)} can't be written to"


def backups_problem() -> str | None:
    """Why backups can't be saved now, or None. The default folder is made when it's first needed; a picked
    one has to be there already."""
    if RUN.backups == DEFAULT_BACKUPS:
        return None
    if not RUN.backups.is_dir():
        return folder_problem(RUN.backups) or "it isn't there"
    return None if os.access(RUN.backups, os.W_OK) else "it can't be written to"


def ask_backups_folder(root: Path, *, size: int = 0):
    """"Save the backup where?", starting at the folder in use: the folder picked, or BACK. Nothing is made or
    remembered yet; use_backups_folder does that once the backup goes ahead. Suggested: the folder in use, the
    default, other drives (not the card being backed up), Desktop and Documents. `size`: an archive about that big
    goes there, so a FAT drive is refused when it's over 4 GB."""
    places = [(tilde(RUN.backups) + "/", "in use")]
    if RUN.backups != DEFAULT_BACKUPS:
        places.append((tilde(DEFAULT_BACKUPS) + "/", "the default, beside the script"))
    places += [(str(c.mount) + "/", f"{c.kind} · {human(c.free)} free") for c in list_cards() if not _under(root, c.mount)]
    places += [(tilde(p) + "/", "") for p in (HOME / "Desktop", HOME / "Documents") if p.is_dir()]
    seen = set()
    places = [(path, label) for path, label in places if not (path in seen or seen.add(path))]  # the first one wins

    def check(path: Path) -> str | None:
        if _under(path, root):
            return "That's inside what's being changed. Pick a folder outside it."
        problem = folder_problem(path)
        return f"Can't save there: {problem}." if problem else too_big_for(path, size)

    return ask_path("Save the backup where?", tilde(RUN.backups), places, books=False, check=check, must_exist=False)


def use_backups_folder(state: dict, picked: Path) -> Path:
    """Backups go to `picked` from now on, for every backup: made if it isn't there, and remembered (picking
    the default again forgets the setting)."""
    picked.mkdir(exist_ok=True)
    if _under(picked, RUN.backups) and _under(RUN.backups, picked):
        return RUN.backups
    before = RUN.backups
    if _under(picked, DEFAULT_BACKUPS) and _under(DEFAULT_BACKUPS, picked):
        RUN.backups = DEFAULT_BACKUPS
        state.pop("backups", None)
    else:
        RUN.backups = picked
        state["backups"] = str(picked)
    if save_state(state):
        done(f"Backups go to {esc(tilde(RUN.backups))} from now on")
    else:
        warn(f"Backups go to {esc(tilde(RUN.backups))} for this run, but {esc(tilde(STATE_FILE))} couldn't be saved, "
             "so the next run uses the folder from before.")
    if any(before.glob("*/*/.source.json")):
        say(f"[hint]Backups already saved stay in {esc(tilde(before))}. Restore can look there.[/]")
    return RUN.backups


def _same_source(note: Path, root: Path, card: Card | None) -> bool:
    try:
        saved = json.loads(note.read_text())
    except (OSError, ValueError):
        return False
    if card and card.uuid:
        return saved.get("card_uuid") == card.uuid
    path = Path(saved.get("path") or "/nonexistent")  # a folder, or a card with no ID: where it was
    return not saved.get("card_uuid") and _under(path, root) and _under(root, path)


def backup_homes(root: Path, label: str, card: Card | None):
    """Today's backup sets for this card or folder, in order: '<label>', '<label> (2)', … A set that
    belongs to another card or folder with the same name is passed over, so the two never mix."""
    number = 1
    while True:
        home = backup_home(label if number == 1 else f"{label} ({number})")
        note = home / ".source.json"
        if not note.exists():
            home.mkdir(parents=True, exist_ok=True)
            note.write_text(json.dumps({"path": str(root), "card_uuid": card.uuid if card else ""}, indent=2))
            yield home
        elif _same_source(note, root, card):
            yield home
        number += 1


def _digest(path: Path) -> bytes:
    with open(path, "rb") as source:
        return hashlib.file_digest(source, "sha256").digest()



def save_original(path: Path, root: Path, label: str, card: Card | None) -> Path:
    """Copy a book into today's backups before it changes, and return where the copy is. An identical
    copy already there counts. A different book that had the same path earlier today goes into the
    next set, so no version is lost."""
    rel = path.relative_to(root).as_posix()
    digest = _digest(path)
    for home in backup_homes(root, label, card):
        target = home / rel
        if target.exists():
            if _digest(target) == digest:
                return target
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        temp = target.with_name(f".{target.name}.part")
        try:
            copy_durably(path, temp)
            if _digest(temp) != digest:
                raise SafetyError(f"Couldn't save a copy of {rel} before changing it.")
            os.replace(temp, target)
        except BaseException:
            with suppress(OSError):
                temp.unlink(missing_ok=True)
            raise
        return target
    raise AssertionError("unreachable")  # backup_homes never ends


def device_record_paths(root: Path) -> list[str]:
    """The X4's records worth keeping, as paths on the card: its recent list, open book, bookmarks and every book's
    progress. Its caches are left out; it rebuilds them."""
    device = root / DEVICE_DIR
    if not device.is_dir():
        return []
    found = [f"{DEVICE_DIR}/{name}" for name in ("recent.json", "state.json") if (device / name).is_file()]
    with suppress(OSError):  # the folder appears with the first bookmark
        found += sorted(f"{DEVICE_DIR}/bookmarks/{entry.name}" for entry in os.scandir(device / "bookmarks")
                        if entry.is_file() and not entry.name.startswith("."))
    found += sorted(f"{DEVICE_DIR}/{path.parent.name}/progress.bin" for path in device.glob("*_*/progress.bin"))
    return found


def save_device_records(card: Card) -> Path | None:
    """The X4's recent list, open book, bookmarks and every book's progress, as they are right now, into today's
    set for this card."""
    records = device_record_paths(card.mount)
    if not (card.mount / DEVICE_DIR).is_dir():
        return None
    target = next(backup_homes(card.mount, card.name, card)) / f".device-{datetime.now(UTC).astimezone().strftime('%H%M%S')}"
    target.mkdir(parents=True, exist_ok=True)
    for rel in records:
        copy = target / rel.removeprefix(DEVICE_DIR + "/")
        copy.parent.mkdir(exist_ok=True)
        copy_durably(card.mount / rel, copy)
    return target


def copy_durably(source, target) -> None:
    """A backup copy, on disk before the card changes."""
    shutil.copyfile(source, target)
    with open(target, "rb") as copy:
        durable(copy)



# ── Writing to the card ───────────────────────────────────────────────────────

def put_book(root: Path, rel: str, data: bytes, *, card: Card | None, records: DeviceRecords | None, label: str,
             backup: bool, keep_progress: bool) -> None:
    """One book into place: the card checked, the original saved, the book swapped in and the X4's
    records brought in line, with Ctrl-C held off for the part that has to happen together."""
    dest = root / rel
    if rel.startswith("/") or ".." in rel.split("/") or not _under(dest, root):
        raise SafetyError(f"{rel} would land outside {root}.")
    if card:
        assert_card(card)
    with ctrl_c_shield():
        on_card(dest.parent).mkdir(parents=True, exist_ok=True)
        if backup and dest.is_file():
            save_original(dest, root, label, card)
        write_book(dest, data)
        if records:
            reset_book_records(root, rel, keep_progress=keep_progress)
            records.move(rel, rel)  # the X4's own entries for it now name what macOS wrote
            records.save()
        item_done()


def write_book(dest: Path, data: bytes) -> None:
    """Write under a temporary dot-name beside dest, flushed to the card, then swap it in, so an
    interruption never leaves half a book. The original is untouched until the swap."""
    dest = on_card(dest)
    temp = dest.with_name(f".{dest.name}.part")
    had_original = dest.exists()
    try:
        with open(temp, "wb") as out:
            out.write(data)
            out.flush()
            os.fsync(out.fileno())
        if had_original:
            _clear_flags(dest)  # a locked book can't be replaced otherwise
        card_rename(temp, dest)
    except BaseException:
        # FAT's rename removes the original first: if it's gone, the .part may be the only copy, so it stays
        # for purge_sidecars to report; otherwise nothing is lost by tidying it away
        if dest.exists() or not had_original:
            with suppress(OSError):
                temp.unlink(missing_ok=True)
        raise


def is_appledouble(path: str) -> bool:
    """A ._ file macOS made, told by its header: the temporary name of a book called "_Name" starts "._" too."""
    try:
        with open(path, "rb") as handle:
            return handle.read(4) in (b"\x00\x05\x16\x07", b"")  # its header, or emptied
    except OSError:
        return False


def is_junk(path: str) -> bool:
    name = os.path.basename(path)
    return name in JUNK_FILES or (name.startswith("._") and is_appledouble(path))


def purge_sidecars(root: Path) -> list[str]:
    """._ AppleDouble files, .DS_Store and .apdisk (hidden folders skipped, except .crosspoint and the X4's sleep
    folders, which Restore writes into), and .part files whose finished book is beside them. Any other temporary
    file or folder may be the only copy an interrupted swap or rename left, so it stays; those come back as a list."""
    leftovers = []
    for dirpath, dirnames, filenames in os.walk(root):
        leftovers += [os.path.relpath(os.path.join(dirpath, d), root) for d in dirnames
                      if re.fullmatch(r"\.(.+)\.(renaming|moving)", d)]  # a folder's, holding its books
        top = dirpath == os.fspath(root)
        dirnames[:] = [d for d in dirnames
                       if not d.startswith(".") or d == DEVICE_DIR or (top and d.casefold() in SLEEP_DIRS)]
        for name in filenames:
            path = os.path.join(dirpath, name)
            temporary = re.fullmatch(r"\.(.+)\.(part|renaming|moving)", name)
            if is_junk(path) or \
                    (temporary and temporary.group(2) == "part" and os.path.exists(os.path.join(dirpath, temporary.group(1)))):
                LOG.debug("   remove %s", path)
                try:
                    os.unlink(path)
                except OSError:
                    pass
            elif temporary:
                leftovers.append(os.path.relpath(path, root))
    return leftovers


def remove_empty_folders(root: Path, rel_dir: str) -> None:
    """Empty folders left behind, up to but never including a top-level folder like [ Fantasy ]."""
    while rel_dir and "/" in rel_dir:
        folder = root / rel_dir
        if folder.is_dir():
            with os.scandir(folder) as entries:
                if any(not is_junk(e.path) for e in entries):
                    return
            _clear_flags(on_card(folder))  # a lock would stop the delete halfway
            shutil.rmtree(folder)
        rel_dir = posixpath.dirname(rel_dir)


def batch(items: list, verb: str, name=lambda item: item, *, shielded: bool = True):
    """Each item in turn under a progress bar, keeping count so a stop can say how far it got. `shielded`:
    each item is written under ctrl_c_shield, so the bar says Ctrl-C waits for it."""
    with progress_bar() as bar:
        task = bar.add_task("", total=len(items), detail="", note="")
        for number, item in enumerate(items, 1):
            RUN.work = (number - 1, len(items), verb, name(item))
            bar.update(task, detail=f"{number}/{len(items)} books", note=short(posixpath.basename(name(item)), 32)
                       + ("  Ctrl-C stops after this book" if shielded else ""))
            yield item
            if RUN.work[0] < number:
                item_done()
            bar.advance(task)
    RUN.work = None


def item_done() -> None:
    """The batch's book under way is done: counted as the last step of its shielded change, so a Ctrl-C held
    until then still finds it counted, and logged."""
    if RUN.work:
        done_count, total, verb, name = RUN.work
        LOG.info("   %s %s", verb, name)
        RUN.work = (done_count + 1, total, verb, name)


class RunLog(logging.FileHandler):
    """This run's log. Each cleared sidecar and drive probe is a detail (DEBUG): past RUN_LOG_DETAIL bytes those
    stop, and what was shown, asked and changed carries on, so a run over thousands of books stays small."""

    full = False
    ended = False

    def emit(self, record: logging.LogRecord) -> None:
        if self.ended:
            return
        try:  # tell() flushes, outside logging's own error handling: a full disk must never stop the run
            size = self.stream.tell() if self.stream is not None else 0
        except (OSError, ValueError):
            return
        if size > RUN_LOG_LIMIT:
            self.ended = True
            super().emit(logging.makeLogRecord({
                "msg": "   … past %s: nothing more is logged this run", "args": (human(RUN_LOG_LIMIT),),
                "levelno": logging.INFO, "levelname": "INFO"}))
            return
        past = record.levelno < logging.INFO and size > RUN_LOG_DETAIL
        if past:
            if not self.full:
                self.full = True
                super().emit(logging.makeLogRecord({
                    "msg": "   … past %s: each file isn't logged from here", "args": (human(RUN_LOG_DETAIL),),
                    "levelno": logging.INFO, "levelname": "INFO"}))
            return
        super().emit(record)


def start_log(argv: list[str]) -> None:
    """This run's log: every line shown, every question and its answer, every command run and how it ended, and
    what changed on the card. On unless Settings turned it off. The oldest logs are deleted to keep them all under
    LOGS_SPACE, with room for this one. One that can't be written never stops the run."""
    folder = logs_folder()
    try:
        folder.mkdir(parents=True, exist_ok=True)
        prune_logs(LOGS_SPACE - RUN_LOG_LIMIT)
        path = folder / f"{datetime.now().strftime('%Y-%m-%d %H.%M.%S')}.log"  # local time: a name people read
        handler = RunLog(path, encoding="utf-8", errors="backslashreplace")
    except OSError:
        return
    handler.setFormatter(logging.Formatter("%(asctime)s  %(message)s", "%H:%M:%S"))
    stop_log()
    LOG.handlers[:] = [handler]
    LOG.setLevel(logging.DEBUG)
    RUN.log = path
    LOG.info("xteink-manager %s · %s · Python %s · %s · started %s", VERSION, " ".join(argv) or "the menu",
             platform.python_version(), platform.platform(), datetime.now(UTC).isoformat(timespec="seconds"))


def logs_folder() -> Path:
    """Where the logs go: beside the state file, wherever that is."""
    return STATE_FILE.parent / "logs"


def stop_log() -> None:
    """No log from here on. A handler that drops everything takes the file's place, so nothing reopens it, and
    Python never prints a record itself."""
    for handler in LOG.handlers:
        handler.close()
    LOG.handlers[:] = [logging.NullHandler()]
    RUN.log = None


def saved_logs() -> list[Path]:
    """The logs kept, oldest first: their names are dated."""
    try:
        return sorted(logs_folder().glob("*.log"))
    except OSError:
        return []


def prune_logs(room: int) -> None:
    """Delete the oldest logs until the rest take `room` bytes at most."""
    total = 0
    for log in reversed(saved_logs()):
        with suppress(OSError):
            total += log.stat().st_size
            if total > room:
                log.unlink()


def stopped(message: str, code: int) -> int:
    """How every interrupted run ends: how far it got, writes flushed, whether the card is still in."""
    if RUN.work:
        _line("│", "rail", f"{RUN.work[0]:,} of {RUN.work[1]:,} books {RUN.work[2]} before it stopped; the rest weren't touched.",
              errors)
    os.sync()
    if RUN.card_in_use:
        warn("The card wasn't ejected. Writes are flushed; eject it before you pull it out.")
    if RUN.log:
        _line("│", "rail", f"[hint]What happened is in {esc(tilde(RUN.log))}[/]", errors)
    outro(message, good=False, to=errors)
    return code


class Interrupted(KeyboardInterrupt):
    """A stop by signal (SIGTERM, a closed terminal), handled as Ctrl-C is, so every cleanup on the way out runs."""

    def __init__(self, signum: int):
        super().__init__(signum)
        self.signum = signum


def stop_on_signal(signum: int, frame) -> None:
    raise Interrupted(signum)


@contextmanager
def ctrl_c_shield():
    """While a book and its records change together, Ctrl-C, Ctrl-Z, a closed terminal and SIGTERM can't cut
    in: stopping halfway could leave a book and its progress apart. Ctrl-Z is ignored. A Ctrl-C pressed
    meanwhile is read as a key, and SIGTERM, SIGHUP (or, with no terminal, SIGINT) are noted; any of them
    stops the run afterwards."""
    fd = sys.stdin.fileno() if sys.stdin is not None and sys.stdin.isatty() else None
    saved_tty = termios.tcgetattr(fd) if fd is not None else None
    noted = []
    ignored = (signal.SIGINT, signal.SIGTSTP) if fd is not None else (signal.SIGTSTP,)
    saved = {sig: signal.signal(sig, signal.SIG_IGN) for sig in ignored}
    for sig in {signal.SIGTERM, signal.SIGHUP, signal.SIGINT} - set(ignored):  # with no terminal, SIGINT too
        saved[sig] = signal.signal(sig, lambda signum, frame: noted.append(signum))
    pressed = b""
    try:
        if saved_tty:
            quiet = termios.tcgetattr(fd)
            quiet[3] &= ~(termios.ISIG | termios.ICANON | termios.ECHO)  # ^C arrives as a byte, readable at once
            quiet[6][termios.VMIN], quiet[6][termios.VTIME] = 0, 0
            termios.tcsetattr(fd, termios.TCSANOW, quiet)
        yield
    finally:
        try:
            if saved_tty:
                with suppress(OSError):
                    while chunk := os.read(fd, 1024):
                        pressed += chunk
                with suppress(OSError, termios.error):  # a terminal closed meanwhile can't be reset
                    termios.tcflush(fd, termios.TCIFLUSH)  # keys typed meanwhile can't answer the next prompt
                    termios.tcsetattr(fd, termios.TCSANOW, saved_tty)
        finally:
            for sig, handler in saved.items():
                signal.signal(sig, handler)
    if noted:
        raise Interrupted(noted[0])
    if b"\x03" in pressed:
        raise KeyboardInterrupt


def can_eject() -> bool:
    """Whether a card can be ejected from here: diskutil on macOS, udisks2 on Linux. Without udisks2, unmounting
    takes root, so the card simply stays mounted and is never offered for ejecting."""
    return IS_MAC or bool(shutil.which("udisksctl"))


def eject_card(card: Card) -> bool:
    """Eject the whole card. On Linux, unmounted is already safe to pull; power-off is a bonus."""
    os.sync()
    if IS_MAC:
        ok = run(["diskutil", "eject", card.whole or str(card.mount)]).returncode == 0
    else:
        if os.path.ismount(card.mount) and shutil.which("udisksctl"):
            run(["udisksctl", "unmount", "--no-user-interaction", "-b", card.device])
        ok = not os.path.ismount(card.mount)
        if ok and shutil.which("udisksctl"):
            run(["udisksctl", "power-off", "--no-user-interaction", "-b", card.whole])
    if ok:  # an ejected card is confirmed again if it comes back
        RUN.active = RUN.card_in_use = RUN.confirmed = None
        RUN.used.pop(card_key(card), None)
    return ok


def card_key(card: Card) -> str:
    return card.uuid or card.device


def finish_card(card: Card | None, state: dict, *, changed: bool, receipt: Receipt | None = None,
                folder: Path | None = None) -> None:
    """Sweep macOS clutter, remember the card, show what changed (the task's `receipt`), then eject it or keep it
    mounted. A folder on this computer just shows its receipt and ends. With no one to ask (no terminal) the
    card stays mounted, as it always has."""
    if card is None:
        if receipt and folder:
            show_receipt(folder.name, receipt)
        outro("Done.")
        return
    RUN.used[card_key(card)] = card
    if changed:
        for leftover in purge_sidecars(card.mount):
            warn(f"Left from an interrupted run, kept in case it's the only copy: {esc(leftover)}")
        remember_card(state, card)
        books = len(list_books(card.mount))
        if RUN.active and RUN.active[0].uuid == card.uuid:
            RUN.active = (RUN.active[0], books)
        if receipt:
            receipt.counts.append(f"{plural(books, 'book')} on the card")
            show_receipt(card.name, receipt)
    if not RUN.interactive or not can_eject() or keep_mounted():
        os.sync()
        if RUN.interactive and RUN.in_menu and can_eject():
            outro("Mounted for the next task. The menu offers to eject it, and asks again before you quit.")
            return
        if RUN.interactive:  # from the command line: the run ends here, so it isn't asked again
            RUN.declined.add(card_key(card))
        outro("Done. Eject the card before you pull it out." if changed else "Done.")
        return
    eject_now(card)


def eject_now(card: Card) -> None:
    """Eject the card, and end the task's block saying how that went."""
    if eject_card(card):
        outro("Ejected. Ready for the X4.")
    else:
        fail("The card didn't eject.")
        outro("Done. Eject the card before you pull it out.", good=False)


def keep_mounted() -> bool:
    """After a task: eject the card, or keep it mounted, from the menu for another task, from the command line
    to look at it first. Esc keeps it."""
    eject, keep = object(), object()
    later = (option("Keep it mounted", keep, "for another task", width=16) if RUN.in_menu
             else option("Leave it mounted", keep, "eject it before you pull it out", width=16))
    return ask_select("Then", [option("Eject", eject, "ready to go back in the X4", width=16), later],
                      on_escape=keep, esc_hint="") is keep


def cards_left_mounted() -> list[Card]:
    """The cards this run used that are still mounted, found by ID as they're mounted now. One ejected outside
    the tool is simply gone. None where it can't eject them."""
    if not RUN.used or not can_eject():
        return []
    mounted = {card_key(card): card for card in list_cards()}
    return [mounted[key] for key in RUN.used if key in mounted]


def cards_waiting() -> list[Card]:
    """The cards to ask about before quitting. At the end of a task run straight from the command line, not the
    one just left mounted: that would ask the same thing twice in a row."""
    return [card for card in cards_left_mounted() if RUN.in_menu or card_key(card) not in RUN.declined]


def before_quitting(state: dict) -> bool:
    """The last step of a run that wasn't stopped: each card it used that's still mounted is named, and ejecting
    it is offered. Yes is the default for the card used last. True when that ended the block."""
    waiting = cards_waiting()
    RUN.task = "Before quitting"
    try:
        for card in waiting:
            warn(f"{esc(card.name)} is still mounted.")
            known = bool(card.uuid) and card.uuid in (state.get("card_uuid"), RUN.confirmed and RUN.confirmed[0])
            if ask_confirm(f"Eject {card.name} before quitting?", known):
                eject_now(card)
            else:
                RUN.declined.add(card_key(card))
                outro(f"{card.name} is still mounted. Eject it before you pull it out.", good=False)
    finally:
        RUN.task = ""
    return bool(waiting)



# ── Running a batch of books ──────────────────────────────────────────────────

@dataclass
class Options:
    task: str | None = None
    path: str | None = None
    dry_run: bool = False
    backup: bool = True
    yes: bool = False
    force: bool = False
    quality: int = JPEG_QUALITY
    keep_fonts: bool = False
    keep_comments: bool = False

    @property
    def settings(self) -> OptimizeSettings:
        return OptimizeSettings(self.quality, not self.keep_fonts, not self.keep_comments)


@dataclass
class Job:
    rel: str                        # where the book is now, relative to its card or folder
    source: Path
    result: Prepared = field(default_factory=Prepared)
    staged: Path | None = None      # the prepared book, kept on this computer until it's written
    dest: str = ""                  # where it's written, relative to the same root
    replaces: bool = False          # a book is already there
    same: bool = False              # …and it's this very book, so there's nothing to write
    keep_progress: bool = True      # the X4's saved page still fits the new book
    other_book: bool = False        # what's there is a different book (another identifier) with this name

    @property
    def size(self) -> int:
        return (self.staged or self.source).stat().st_size


def prepare_books(books: list[tuple[str, Path]], steps: Steps, opts: Options, staging: Path) -> list[Job]:
    """Every book through prepare(), each changed one staged on disk so memory stays small."""
    jobs = []
    sizes = [path.stat().st_size for _, path in books]
    with progress_bar() as bar:
        task = bar.add_task("", total=max(sum(sizes), 1), detail="", note="")
        for number, ((rel, path), size) in enumerate(zip(books, sizes, strict=True), 1):
            bar.update(task, detail=f"{number}/{len(books)} books", note=short(posixpath.basename(rel), 32))
            try:
                raw = path.read_bytes()
            except OSError as error:
                result = Prepared(error=f"couldn't be read ({error.strerror or error})")
            else:
                result = prepare(raw, Path(rel).stem, steps, opts.settings, force=opts.force)
            job = Job(rel, path, result)
            if result.data is not None:
                job.staged = staging / f"{number}.epub"
                job.staged.write_bytes(result.data)
                result.data = None
            jobs.append(job)
            bar.advance(task, size)
    return jobs


def progress_note(card: Card | None, rel: str, keep: bool) -> str:
    """What happens to the X4's saved page, for a book it has opened before."""
    if card is None or not any(record.is_dir() for record in existing_records(card.mount, rel)):
        return ""
    return "reading progress kept" if keep else "chapters changed, so it opens at the start, without bookmarks"


def show_errors(jobs: list[Job]) -> None:
    """Books left out, and why. Any at all count as a failure."""
    if jobs:
        mark_failed()
    listing([(job.rel, f"{esc(job.result.error)}; left as it was") for job in jobs])


def backup_line(opts: Options, what: str = "Originals", *, always: bool = False) -> None:
    """What's saved first, said just before "Go ahead?"; where, once a run, so a long path isn't repeated before
    every change. `always`: saved even with --no-backup, as the X4's records are. A folder that isn't there is left
    to "Go ahead?" to say."""
    if not (opts.backup or always):
        warn(f"--no-backup: {what.lower()} aren't saved anywhere first.")
    elif not backups_problem():
        say(f"[hint]{what} are saved first" + (f", in {esc(tilde(backup_day()))}/" if once("backups folder") else "")
            + ".[/]")


def ask_go(go: str, state: dict, root: Path, *, extra=(), cancel: str = "Back", safe: bool = False,
           saves: bool = True, skip: bool = False):
    """"Go ahead?", the last question before a change: "go", the value of a picked `extra` choice, or BACK.
    When the change `saves` backups and the folder picked for them isn't there (a drive unplugged), going ahead
    isn't offered; another folder is, instead. `safe`: Enter alone picks `cancel`. `skip` (--yes): no question."""
    elsewhere = object()
    while True:
        problem = backups_problem() if saves else None
        if skip:
            if problem:
                raise SafetyError(f"Backups can't be saved to {tilde(RUN.backups)}: {problem}.")
            return "go"
        if problem:
            warn(f"Backups can't be saved to {esc(tilde(RUN.backups))}: {esc(problem)}.")
        choices = ([] if problem else [option(go, "go")]) + list(extra)
        if problem:
            choices.append(option("Save backups somewhere else…", elsewhere))
        choices.append(back() if cancel == "Back" else option(cancel, BACK))
        picked = ask_select("Go ahead?", choices, default=BACK if safe else elsewhere if problem else None)
        if picked is not elsewhere:
            return picked
        with doing("Choosing", "where backups go"):
            if (picked := ask_backups_folder(root)) is not BACK:
                use_backups_folder(state, picked)



def begin_card_changes(card: Card, state: dict) -> DeviceRecords:
    """Right before the first write: the card is still the one picked, the X4's records are saved, and the
    card is noted as changed (for the menu's backup reminder), even if the task is stopped partway."""
    assert_card(card)
    remember_card(state, card)
    RUN.card_in_use = card
    save_device_records(card)
    return DeviceRecords(card.mount)



# ── Task: add books ───────────────────────────────────────────────────────────

def ask_genre(message: str, genres: list[str], *, allow_each: bool):
    """A genre folder from the card's, or a new one (remembered for the next book). None means
    "pick for each book"; BACK means back out."""
    each, new = object(), object()
    choices = [option(name, name, plain=True) for name in genres] + ([divider()] if genres else [])
    if allow_each:
        choices.append(action_choice("Pick for each book", each, "→"))
    choices += [action_choice("New genre folder…", new, "+"), back()]
    while True:
        picked = ask_select(message, choices, search=True)
        if picked is not new:
            return None if picked is each else picked
        typed = ask_text("New genre folder, like [ Poetry ]", validate=lambda raw: name_problem(raw.strip()) or (
            SYSTEM_FOLDER if system_path(raw.strip()) else True))
        if typed is BACK:
            continue
        name = typed.strip()
        if name not in genres:
            genres.append(name)
        return name


def place_books(card: Card, jobs: list[Job], genre: str | None, genres: list[str]) -> bool:
    """Every book's place on the card. With no genre for the batch, each book's is asked by its title, and
    Back returns to the book before. False when backing out of the first one."""
    picked, index = [], 0
    while index < len(jobs):
        if genre:
            picked.append(genre)
            index += 1
            continue
        meta = jobs[index].result.metadata
        title, author = meta.get("title") or Path(jobs[index].rel).stem, author_folder(meta)
        choice = ask_genre(f"Genre for {short(title)}" + (f" ({short(author, 30)})" if author else "") + "?",
                           genres, allow_each=False)
        if choice is BACK:
            if index == 0:
                return False
            picked.pop()
            index -= 1
            continue
        picked.append(choice)
        index += 1
    planned = set()
    for job, book_genre in zip(jobs, picked):
        plan_destination(card, job, book_genre, planned)
    return True


def plan_destination(card: Card, job: Job, genre: str, planned: set[str]) -> None:
    dest = place_book(card.mount, genre, job.result.metadata, Path(job.rel).stem)
    stem, number = dest[:-len(".epub")], 2
    while fold(dest) in planned or (card.mount / card_spelling(card.mount, dest)).is_dir():  # a folder named Title.epub
        dest, number = f"{stem} ({number}).epub", number + 1
    for part in dest.split("/"):
        if problem := name_problem(part):
            raise SafetyError(f"Can't put a book at {dest}: {problem}")
    set_destination(card.mount, job, dest)
    planned.add(fold(dest))


def card_spelling(root: Path, rel: str) -> str:
    """A path with every part that already exists spelled as the card lists it."""
    parts, found = rel.split("/"), []
    for i, part in enumerate(parts):
        match = resolve_on_card(root, "/".join([*found, part]))
        if match is None:
            return "/".join([*found, *parts[i:]])
        found = match.split("/")
    return "/".join(found)


def set_destination(root: Path, job: Job, dest: str) -> None:
    """Where a book goes, spelled as the card lists it, and what's there now: nothing, this very book,
    another version of it (whose saved page still fits if the reading order is the same), or a different
    book with the same name (another identifier). Another kind of file the X4 opens is the same or not, byte for byte."""
    job.dest = card_spelling(root, dest)
    job.replaces = (root / job.dest).is_file()
    if not is_book_name(job.dest):
        job.same = job.keep_progress = job.replaces and (root / job.dest).read_bytes() == (job.staged or job.source).read_bytes()
        return
    old = new = None
    if job.replaces:
        try:
            old, new = read_epub((root / job.dest).read_bytes()), read_epub((job.staged or job.source).read_bytes())
        except BAD_ZIP:
            pass
    job.same = old is not None and old == new
    job.keep_progress = old is not None and spine_paths(old) == spine_paths(new)
    ids = (book_id(old), book_id(new)) if old is not None else (None, None)
    job.other_book = None not in ids and ids[0] != ids[1]


def book_id(entries: dict[str, bytes]) -> str | None:
    opf = find_opf(entries)
    return extract_identifier(decode_text(entries[opf])) if opf else None


def show_add_review(card: Card, jobs: list[Job], failed: list[Job], opts: Options) -> None:
    todo = [job for job in jobs if not job.same]
    total = sum(job.size for job in todo)
    boxed([Text(f"Copy {plural(len(todo), 'book')} to {card.name} · {human(total)} of {human(card.free)} free")])
    for job in jobs:
        if job.same:
            say(f"  [hint]= {esc(job.dest)}[/]")
            say("      [hint]already on the card, exactly the same; skipped[/]")
            continue
        say(f"  {'[warn]↻[/]' if job.replaces else '[ok]+[/]'} {esc(job.dest)}")
        if job.result.summary():
            LOG.info("   %s: %s", job.dest, job.result.summary())
        details = [job.result.brief() or "copied as it is"]
        if job.replaces and not job.other_book:
            details.append("replaces the copy on the card")
            if note := progress_note(card, job.dest, job.keep_progress):
                details.append(note)
        say(f"      [hint]{esc(' · '.join(details))}[/]")
        if job.other_book:
            say("      [warn]replaces a different book with the same name; pick Change to keep both[/]")
        genre = job.dest.split("/")[0]
        if "/" in job.dest and not (card.mount / genre).is_dir():
            say(f"      [warn]makes a new folder, {esc(genre)}[/]")
    show_errors(failed)
    if any(job.replaces and not job.same for job in jobs):
        backup_line(opts, "Replaced books")
    else:
        backup_line(opts, "The X4's reading progress and bookmarks", always=True)


def change_destination(card: Card, jobs: list[Job]) -> None:
    job = ask_select("Change which?", [*(option(j.dest, j, plain=True) for j in jobs), divider(), back()],
                     search=True, echo=False)
    if job is BACK:
        return
    with doing("Changing where it goes", job.dest):
        others = {fold(j.dest) for j in jobs if j is not job}

        def validate(raw: str):
            dest = raw.strip().strip("/")
            if not is_book_name(posixpath.basename(dest)):
                return "End it with .epub, like [ Fantasy ]/Author/Title.epub"
            for part in dest.split("/"):
                if problem := name_problem(part):
                    return problem
            if system_path(dest):
                return SYSTEM_FOLDER
            if (card.mount / card_spelling(card.mount, dest)).is_dir():
                return "There's a folder with that name there."
            return "Another book is going there." if fold(dest) in others else True

        raw = typed_field("New place on the card", "Tab completes folders", default=job.dest, validate=validate,
                          completer=CardCompleter(card.mount, "either"), complete_style=CompleteStyle.COLUMN)
        if raw is BACK:
            return
        set_destination(card.mount, job, raw.strip().strip("/"))
        _answered("New place on the card", job.dest)


def task_add(opts: Options, state: dict):
    source = path_arg(opts)
    if source and card_for(source):
        raise SafetyError("Those books are on a card already. Pick books on this computer.")
    card = choose_card(state)
    if card is None:
        return BACK
    if source is None:
        last = state.get("library")
        places = [(tilde(last) + "/", "last used")] if last else []
        places += [(tilde(p) + "/", "") for p in (HOME / "Downloads", HOME / "Desktop") if p.is_dir()]
        on_cards = card_device_ids()  # looked up once: the check runs on every keystroke
        source = ask_path("Books to add?", tilde(last) if last else "", places, books=True,
                          check=lambda p: "That's on a card. Pick books on this computer."
                          if os.stat(p).st_dev in on_cards else None)
        if source is BACK:
            return BACK
    check_local(source, backups_ok=True)
    root = source if source.is_dir() else source.parent
    books = [(rel, root / rel) for rel in list_books(root, "" if source.is_dir() else source.name)]
    if source.is_dir():  # Apple Books keeps a book as a folder named like a file; it needs exporting first
        packages = [source] if is_book_name(source.name) else sorted(p for p in source.rglob("*.epub") if p.is_dir())
        if packages:
            warn(f"{plural(len(packages), 'Apple Books folder')} left out, like {esc(packages[0].name)}. "
                 "Export it from Books as a file first.")
    if not books:
        fail("No .epub books there.")
        outro("Nothing was copied.", good=False)
        return None
    say(f"{plural(len(books), 'book')} found")

    with doing("Adding", f"{plural(len(books), 'book')} from {tilde(source)}"):
        scans = 0
        for _, path in books:
            try:
                scans += looks_like_scan(read_epub(path.read_bytes()))
            except BAD_ZIP:
                pass
        width = 38 if scans else 16
        choices = [option("Optimize, and clean archive.org scans" if scans else "Optimize", Steps(True, True),
                          f"{scans} of {len(books)} look like archive.org scans" if scans else "as the firmware's Optimize EPUB",
                          width=width)]
        if scans:
            choices.append(option("Optimize only", Steps(False, True), "leave the scans as they are", width=width))
        choices += [option("Copy as they are", Steps(False, False), "no changes", width=width), back()]
        if (steps := ask_select("Prepare them first?", choices)) is BACK:
            return BACK

        with tempfile.TemporaryDirectory(prefix="xteink-") as staging:
            jobs = prepare_books(books, steps, opts, Path(staging))
            failed = [job for job in jobs if job.result.error]
            jobs = [job for job in jobs if not job.result.error]
            if not jobs:
                show_errors(failed)
                outro("Nothing was copied.", good=False)
                return None
            done(f"Prepared {plural(len(jobs), 'book')}" + (f", {len(failed)} left out" if failed else ""))

            genres = [e.name for e in visible_entries(card.mount) if e.is_dir() and list_books(card.mount, e.name)]
            action = None
            while action != "go":  # the genre, then the review; Back at "Go ahead?" comes back here
                genre = ask_genre("Genre folder for these books?" if len(jobs) > 1 else "Genre folder?", genres,
                                  allow_each=len(jobs) > 1)
                if genre is BACK:
                    return BACK
                if not place_books(card, jobs, genre, genres):
                    continue
                while True:
                    show_add_review(card, jobs, failed, opts)
                    todo = [job for job in jobs if not job.same]
                    if not todo:
                        outro("Nothing to copy: the card already has these books.")
                        return None
                    if sum(job.size for job in todo) > card.free:
                        fail("Not enough free space on the card.")
                        outro("Nothing was copied.", good=False)
                        return None
                    if opts.dry_run:
                        outro("Preview only. Nothing was copied.")
                        return None
                    action = ask_go(f"Copy {plural(len(todo), 'book')}", state, card.mount, skip=opts.yes,
                                    extra=[option("Change a name or folder", "change")])
                    if action != "change":
                        break
                    change_destination(card, jobs)

            records = begin_card_changes(card, state)
            for job in batch(todo, "copied", lambda job: job.dest):
                put_book(card.mount, job.dest, (job.staged or job.source).read_bytes(), card=card, records=records,
                         label=card.name, backup=opts.backup, keep_progress=job.keep_progress)
        done(f"Copied {plural(len(todo), 'book')}")
        save_state(state, library=str(root))
        receipt = Receipt()
        for job in todo:
            receipt.add("↻" if job.replaces else "+", job.dest, "replaced" if job.replaces else "added")
        finish_card(card, state, changed=True, receipt=receipt)
        return None



# ── Task: prepare books (clean and/or optimize in place) ──────────────────────

STEP_CHOICES = [
    ("Optimize, and clean archive.org scans", Steps(True, True), "recommended"),
    ("Optimize only", Steps(False, True), "as the firmware's Optimize EPUB"),
    ("Clean archive.org scans only", Steps(True, False), "repairs page-scan books, nothing else"),
]


def task_prepare(opts: Options, state: dict, steps: Steps | None):
    if target := path_arg(opts):
        if target.is_file() and not is_book_name(target.name):
            raise SafetyError(f"Not a folder or an .epub book: {tilde(target)}")
        card, root, start = locate(target)
        if card:
            show_card(card, state, chosen=True)
    else:
        where = ask_select("Prepare which books?", [option("On the card", "card", "all of it, a folder or one book", width=18),
                                                    option("On this computer", "local", "a folder or one .epub", width=18),
                                                    back()])
        if where is BACK:
            return BACK
        if where == "card":
            if (card := choose_card(state)) is None:
                return BACK
            whole = ask_select("Which part?", [option("The whole card", True), option("A folder or one book", False),
                                               back()])
            if whole is BACK:
                return BACK
            root, start = card.mount, "" if whole else ask_card_path(card, "Which folder or book?", want="either")
            if start is None:
                return BACK
        else:
            on_cards = card_device_ids()  # looked up once: the check runs on every keystroke

            def not_here(path: Path) -> str | None:
                if os.stat(path).st_dev in on_cards:
                    return "That's on a card. Go back and pick On the card."
                return "That's in the backups folder. Restore puts books back from there." if _under(path, RUN.backups) else None

            target = ask_path("Which folder or book?", "", [(tilde(p) + "/", "") for p in (HOME / "Downloads", HOME / "Desktop")
                                                              if p.is_dir()], books=True, check=not_here)
            if target is BACK:
                return BACK
            card, root, start = locate(target)

    with doing("Preparing", (start + ("/" if (root / start).is_dir() else "") if start else f"all of {card.name}")
               if card else tilde(root / start)):
        if steps is None:
            steps = ask_select("Steps?", [*(option(label, value, hint, width=38) for label, value, hint in STEP_CHOICES),
                                          back()])
            if steps is BACK:
                return BACK
        label = card.name if card else root.name
        books = [(rel, root / rel) for rel in list_books(root, start)]
        if links := [rel for rel, path in books if path.is_symlink()]:  # replacing one would replace the link
            books = [(rel, path) for rel, path in books if not path.is_symlink()]
            warn(f"Left {plural(len(links), 'linked book')} as they are; prepare the books they link to instead.")
        if not books:
            fail("No .epub books there.")
            outro("Nothing changed.", good=False)
            return None

        with tempfile.TemporaryDirectory(prefix="xteink-") as staging:
            say(f"[hint]Checking {plural(len(books), 'book')}. Nothing is written yet.[/]")
            jobs = prepare_books(books, steps, opts, Path(staging))
            changed = [job for job in jobs if job.staged]
            failed = [job for job in jobs if job.result.error]
            reasons = Counter(job.result.unchanged for job in jobs if not job.staged and not job.result.error)

            done(f"{plural(len(changed), 'book')} would change" +
                 "".join(f" · {count:,} {reason}" for reason, count in reasons.most_common()))
            for job in changed:
                job.dest, job.keep_progress = job.rel, not job.result.spine_changed
                LOG.info("   %s: %s", job.rel, job.result.summary())
                details = [job.result.brief()]
                if note := progress_note(card, job.rel, job.keep_progress):
                    details.append(note)
                say(f"  [accent]↻[/] {esc(job.rel)}")
                say(f"      [hint]{esc(' · '.join(details))}[/]")
            show_errors(failed)
            if opts.force and steps.optimize and changed:
                warn("--force optimizes books again: their images are re-encoded, losing a little more detail.")
            if not changed:
                outro("Nothing to change.")
                return None
            backup_line(opts)
            if opts.dry_run:
                outro("Preview only. Nothing was written.")
                return None
            if ask_go(f"Replace {plural(len(changed), 'book')}", state, root, saves=card is not None or opts.backup,
                      skip=opts.yes) is BACK:
                return BACK

            records = begin_card_changes(card, state) if card else None
            before = after = 0
            for job in batch(changed, "replaced", lambda job: job.dest):
                before += (root / job.dest).stat().st_size
                data = job.staged.read_bytes()
                put_book(root, job.dest, data, card=card, records=records, label=label, backup=opts.backup,
                         keep_progress=job.keep_progress)
                after += len(data)
        done(f"Replaced {plural(len(changed), 'book')} · {human(before)} → {human(after)}")
        receipt = Receipt()
        for job in changed:
            receipt.add("↻", job.dest, job.result.brief())
        finish_card(card, state, changed=True, receipt=receipt, folder=root)
        return None



# ── Task: move or rename ──────────────────────────────────────────────────────

def rename_on_card(root: Path, old_rel: str, new_rel: str) -> None:
    """A rename FAT can do, never onto another file. The same name in another case or accent spelling
    goes through a temporary name, since FAT sees both as one file; if that fails halfway, it's undone."""
    src, dst = root / old_rel, root / new_rel
    if dst.exists() and not os.path.samefile(src, dst):
        raise SafetyError(f"{new_rel} is already on the card.")
    _clear_flags(on_card(src))  # a locked book or folder can't be renamed otherwise
    if dst.exists():
        temp = src.with_name(f".{src.name}.renaming")
        card_rename(src, temp)
        try:
            card_rename(temp, dst)
        except OSError:
            card_rename(temp, src)
            raise
    else:
        card_rename(src, dst)


def move_item(card: Card, records: DeviceRecords, what: str, new_rel: str) -> None:
    """Move a book or folder, then every book's cache, progress and bookmarks inside it. If the
    records can't follow, everything is put back."""
    root = card.mount
    books = list_books(root, what, kinds=RECORD_PREFIXES, strict=True) if (root / what).is_dir() else [what]
    on_card(root / posixpath.dirname(new_rel)).mkdir(parents=True, exist_ok=True)
    rename_on_card(root, what, new_rel)
    moved = []
    try:
        for book in books:
            new_book = new_rel + book[len(what):]
            for record in existing_records(root, book):  # composed spelling first, so it wins a tie
                target = _counterpart(record, root, new_book)
                if target not in {t for _, t in moved} and _move_aside(record, target):
                    moved.append((record, target))
    except OSError as error:
        try:
            for record, target in reversed(moved):
                _move_aside(target, record)
            rename_on_card(root, resolve_on_card(root, new_rel) or new_rel, what)
            remove_empty_folders(root, posixpath.dirname(new_rel))  # any the move made
        except OSError as undo:
            raise SafetyError(f"Moving {what} failed ({error.strerror or error}) and couldn't be undone "
                              f"({undo.strerror or undo}). It's at {new_rel}; its progress may not have followed.") from error
        raise
    records.move(what, new_rel)
    records.save()


def ask_new_place(card: Card, what: str) -> str | None:
    """Where a book or folder goes: renamed where it is, or moved to another folder with its name (a new
    name is asked for only if that one's taken there). None to go back."""
    root, is_dir = card.mount, (card.mount / what).is_dir()
    parent, name = posixpath.split(what)
    shown = what + "/" if is_dir else what

    def fits_in(folder: str):
        def validate(raw: str):
            text = with_extension(raw, name, is_dir)
            if problem := name_problem(text):
                return problem
            new_rel = posixpath.join(folder, text)
            if system_path(new_rel):
                return SYSTEM_FOLDER
            taken = resolve_on_card(root, new_rel)
            return "That name is already taken there." if taken and nfc(taken) != nfc(what) else True
        return validate

    while True:
        with doing("Move or rename", shown):
            action = ask_select("Do what with it?", [
                option("Rename it", "rename", f"stays in {parent}/" if parent else "stays at the top level", width=9),
                option("Move it", "move", "to another folder; the name stays", width=9),
                back()])
        if action is BACK:
            return None
        with doing("Renaming" if action == "rename" else "Moving", shown):
            folder = parent
            if action == "move":
                folder = ask_card_path(card, "Into which folder?", want="folder", start=parent)
                if folder is None:
                    continue
                new_rel = posixpath.join(folder, name)
                if nfc(folder) == nfc(parent):
                    say("[hint]It's already in that folder.[/]")
                    continue
                if is_dir and nfc(new_rel).startswith(nfc(what) + "/"):
                    warn("A folder can't go inside itself.")
                    continue
                if not resolve_on_card(root, new_rel):
                    return new_rel
                warn(f"{esc(folder or 'The top level')}/ already has a {esc(name)}. Give this one another name.")
            typed = ask_text("New name", default=nfc(name), validate=fits_in(folder))
            if typed is BACK:
                continue
            new_rel = posixpath.join(folder, with_extension(typed, name, is_dir))
            if nfc(new_rel) == nfc(what):
                say("[hint]That's its name already.[/]")
                continue
            return new_rel


def task_move(opts: Options, state: dict):
    given = card_item_arg(opts)
    card = given[0] if given else choose_card(state)
    if card is None:
        return BACK
    if given:
        show_card(card, state, chosen=True)
    root, records, what = card.mount, None, given[1] if given else ""
    receipt = Receipt()
    while True:
        what = what or ask_card_path(card, "Move or rename what?", want="either")
        if not what:
            if not receipt.rows:
                return BACK
            break
        new_rel = ask_new_place(card, what)
        if new_rel is None:
            what = ""
            continue

        parent, folder = posixpath.dirname(what), posixpath.dirname(new_rel)
        renaming, is_dir = nfc(folder) == nfc(parent), (root / what).is_dir()
        with doing("Renaming" if renaming else "Moving", what + "/" if is_dir else what):
            say(f"  {esc(what)}")
            say(f"  [accent]→[/] {esc(new_rel)}")
            if folder and not (root / folder).is_dir():
                warn(f"{esc(folder)} is a new folder; it's made for this.")
            if is_dir:
                books, others = len(list_books(root, what)), len(list_books(root, what, kinds=OTHER_KINDS))
                say(f"[hint]{tally(books, others)} {'goes' if books + others == 1 else 'go'} with it; each keeps its "
                    "progress and bookmarks.[/]")
            else:
                say("[hint]Progress, bookmarks and the recent list follow the book.[/]")
            if records is None:
                backup_line(opts, "The X4's reading progress and bookmarks", always=True)
            if opts.dry_run:
                outro("Preview only. Nothing was changed.")
                return None
            go = ask_go("Rename it" if renaming else "Move it", state, root) == "go"
            if go:
                if records is None:
                    records = begin_card_changes(card, state)
                assert_card(card)
                with ctrl_c_shield():
                    move_item(card, records, what, new_rel)
                remove_empty_folders(root, parent)
                slash = "/" if is_dir else ""
                receipt.add("✎" if renaming else "→", new_rel + slash,
                            f"was {posixpath.basename(what) + slash if renaming else what + slash}")
                done(f"{'Renamed' if renaming else 'Moved'} to {esc(new_rel)}")
        if go and not ask_confirm("Move or rename something else?", False):
            break
        what = ""
    finish_card(card, state, changed=True, receipt=receipt)
    return None



# ── Task: remove books ────────────────────────────────────────────────────────

def task_remove(opts: Options, state: dict):
    given = card_item_arg(opts)
    card = given[0] if given else choose_card(state)
    if card is None:
        return BACK
    if given:
        show_card(card, state, chosen=True)
    root = card.mount
    what = given[1] if given else ask_card_path(card, "Remove which book or folder?", want="either")
    if not what:
        return BACK
    is_dir = (root / what).is_dir()
    with doing("Removing from" if is_dir else "Removing", what + "/" if is_dir else what, red=True):
        if is_dir:
            books = list_books(root, what)
            if not books:
                fail("No books in that folder.")
                outro("Nothing changed.", good=False)
                return None
            picked = ask_checkbox(f"Which books in {short(what)}/?",
                                  [Choice(title=rel[len(what) + 1:], value=rel) for rel in books])
            if picked is BACK:
                return BACK
        elif is_book_name(what):
            picked = [what]
        else:
            raise SafetyError(f"{what} isn't an .epub book.")

        for rel in picked:
            say(f"  [bad]✗[/] {esc(rel)}  [hint]{human((root / rel).stat().st_size)}[/]")
        say("[hint]Their progress, bookmarks and cache go too.[/]")
        backup_line(opts, "Copies")
        if opts.dry_run:
            outro("Preview only. Nothing was removed.")
            return None
        if ask_go(f"Remove {plural(len(picked), 'book')}", state, root, cancel="No", safe=True) is BACK:
            outro("Nothing changed.")
            return None

    records = begin_card_changes(card, state)
    for rel in batch(picked, "removed"):
        assert_card(card)
        with ctrl_c_shield():
            if opts.backup:
                save_original(root / rel, root, card.name, card)
            LOG.info("   remove %s", root / rel)
            _clear_flags(on_card(root / rel))  # a locked book can't be deleted otherwise
            (root / rel).unlink()
            forget_book_records(root, records, rel)
            records.save()
            item_done()
    for folder in sorted({posixpath.dirname(rel) for rel in picked}, key=len, reverse=True):
        remove_empty_folders(root, folder)
    done(f"Removed {plural(len(picked), 'book')}")
    receipt = Receipt()
    for rel in picked:
        receipt.add("−", rel, "removed; a copy is saved" if opts.backup else "removed")
    finish_card(card, state, changed=True, receipt=receipt)
    return None



# ── Archives ──────────────────────────────────────────────────────────────────
# Back up packs the card into one archive the way tecsun-manager packs the radio's: tar + zstd and a SHA-256 checksum
# list in one pass, read back from the drive, then par2 repair data. Until the read-back passes, both files keep a
# .partial name, so a backup that was stopped or didn't check out never looks finished.

PARTIAL = ".partial"


def sidecar(archive: Path, suffix: str) -> Path:
    return archive.with_name(archive.name + suffix)


def have_par2() -> bool:
    return shutil.which("par2") is not None


def install_hint(*names: str) -> str:
    return ("brew install " if IS_MAC else "sudo apt install ") + " ".join(names)


class HashingReader:
    """Wraps a file so tarfile's reads also feed the checksum and the progress bar: one read per file."""

    def __init__(self, source, on_bytes):
        self.source = source
        self.sha = hashlib.sha256()
        self.on_bytes = on_bytes

    def read(self, size: int = -1) -> bytes:
        data = self.source.read(size)
        self.sha.update(data)
        self.on_bytes(len(data))
        return data


class CountingReader:
    """Counts compressed bytes read, so progress follows the archive file itself."""

    def __init__(self, source, on_bytes):
        self.source = source
        self.on_bytes = on_bytes

    def read(self, size: int = -1) -> bytes:
        data = self.source.read(size)
        self.on_bytes(len(data))
        return data

    def readinto(self, buffer) -> int:
        count = self.source.readinto(buffer) or 0
        self.on_bytes(count)
        return count

    def readable(self) -> bool:
        return True

    def close(self) -> None:
        self.source.close()

    @property
    def closed(self) -> bool:
        return self.source.closed


@contextmanager
def open_archive(archive: Path, on_bytes=lambda n: None):
    """Stream a backup archive. Reading on to the very end makes zstd check its own checksum too."""
    with ExitStack() as stack:
        counted = CountingReader(stack.enter_context(open(archive, "rb")), on_bytes)
        stream = stack.enter_context(zstd.ZstdFile(counted, "r"))
        yield stack.enter_context(tarfile.open(fileobj=stream, mode="r|"))
        while stream.read(1 << 20):
            pass


READ_ERRORS = (tarfile.TarError, EOFError, OSError, ValueError, zstd.ZstdError)


def unlistable(name: str) -> bool:
    """A line-based checksum list can't hold a name with a line break. FAT forbids them; other drives may not."""
    return name.splitlines() != [name]


def durable(handle) -> None:
    """Push a file's data all the way to the drive before it counts as written."""
    handle.flush()
    os.fsync(handle.fileno())
    if IS_MAC:
        with suppress(OSError):
            fcntl.fcntl(handle.fileno(), fcntl.F_FULLFSYNC)  # fsync alone stops at the drive's cache on macOS


def write_archive(members: list[tuple[str, Path]], archive: Path, manifest: Path, on_bytes) -> int:
    """tar + zstd and the SHA-256 checksum list in one pass, each file read once, both pushed to the drive.
    `members` are (name in the archive, file). Returns how many names the list had to skip. A stop or a read
    error deletes both, so nothing half-written is left."""
    params = zstd.CompressionParameter
    options = {params.compression_level: ZSTD_LEVEL, params.checksum_flag: 1}
    most_workers = params.nb_workers.bounds()[1]
    if most_workers > 0:
        options[params.nb_workers] = min(os.cpu_count() or 1, most_workers)
    skipped = 0
    try:
        with (open(archive, "wb") as raw,
              open(manifest, "w", encoding="utf-8", errors="surrogateescape", newline="\n") as sums):
            if IS_MAC:
                fcntl.fcntl(raw.fileno(), fcntl.F_NOCACHE, 1)  # not kept in RAM: the read-back has to read the drive
            # dereference: a linked book is stored as the book itself
            with (zstd.ZstdFile(raw, "w", options=options) as compressed,
                  tarfile.open(fileobj=compressed, mode="w|", format=tarfile.PAX_FORMAT, dereference=True) as tar):
                for name, path in members:
                    info = tar.gettarinfo(str(path), arcname=name)
                    with open(path, "rb") as source:
                        reader = HashingReader(source, on_bytes)
                        tar.addfile(info, reader)
                    if unlistable(name):
                        skipped += 1
                    else:
                        sums.write(f"{reader.sha.hexdigest()}  {name}\n")
            durable(raw)
            durable(sums)
            if hasattr(os, "posix_fadvise"):  # Linux: drop the cached copy for the same reason
                os.posix_fadvise(raw.fileno(), 0, 0, os.POSIX_FADV_DONTNEED)
    except BaseException:
        archive.unlink(missing_ok=True)
        manifest.unlink(missing_ok=True)
        raise
    return skipped


def read_manifest(manifest: Path) -> tuple[dict[str, str], int]:
    """Reads `sha256sum` / `shasum -a 256` format. Also counts lines that aren't checksums, so a damaged list can't
    pass quietly."""
    wanted, unreadable = {}, 0
    for line in manifest.read_text(encoding="utf-8", errors="surrogateescape").splitlines():
        if not line.strip():
            continue
        match = re.match(r"^\\?([0-9a-fA-F]{64}) [ *](.+)$", line)
        if match:
            wanted[match.group(2)] = match.group(1).lower()
        else:
            unreadable += 1
    return wanted, unreadable


def archived_rel(name: str) -> str:
    """A name inside a backup archive as a path on the card: what follows the card's name."""
    return name.split("/", 1)[1] if "/" in name else ""


def kinds_line(counts: Counter) -> str:
    """Files counted by classify(), said in the units every count uses: "1,300 books, 1 other file and the X4's
    records"."""
    parts = [plural(counts["book"], "book")]
    if counts["other"]:
        parts.append(plural(counts["other"], "other file"))
    if counts["record"]:
        parts.append("the X4's records")
    return parts[0] if len(parts) == 1 else ", ".join(parts[:-1]) + " and " + parts[-1]


@dataclass
class Checked:
    """What reading a backup archive back found."""
    seen: Counter = field(default_factory=Counter)  # every file in it, by classify()
    ok: Counter = field(default_factory=Counter)    # the ones that match their checksums
    bad: list[str] = field(default_factory=list)
    missing: list[str] = field(default_factory=list)
    unlisted: list[str] = field(default_factory=list)   # present, but the checksum list doesn't know them
    unreadable_lines: int = 0                            # lines in the checksum list that aren't checksums
    damaged_books: list[tuple[str, str]] = field(default_factory=list)  # (name, why) for books opened on the way

    @property
    def passed(self) -> bool:
        return not (self.bad or self.missing or self.unlisted or self.unreadable_lines)


def _sha256(source) -> str:
    sha = hashlib.sha256()
    while chunk := source.read(1 << 20):
        sha.update(chunk)
    return sha.hexdigest()


def verify_archive(archive: Path, manifest: Path | None, on_bytes, *, inspect=frozenset()) -> Checked:
    """Read every file inside the archive and compare it with the checksum list, unpacking nothing. The books named
    in `inspect` (NFC names in the archive) are also opened as Check opens them, from the archive's own copy."""
    checked, wanted = Checked(), {}
    if manifest:
        listed, checked.unreadable_lines = read_manifest(manifest)
        wanted = {nfc(k): v for k, v in listed.items()}
    with open_archive(archive, on_bytes) as tar:
        for member in tar:
            if not member.isfile():
                continue
            key = nfc(member.name)
            source = tar.extractfile(member)
            if key in inspect:
                data = source.read()
                digest = hashlib.sha256(data).hexdigest()
                if damage := check_book(data)[0]:
                    checked.damaged_books.append((member.name, damage))
            else:
                digest = _sha256(source)
            kind = classify(archived_rel(key))
            checked.seen[kind] += 1
            if not manifest:
                continue
            if key not in wanted:
                if not unlistable(member.name):
                    checked.unlisted.append(member.name)
            elif digest == wanted.pop(key):
                checked.ok[kind] += 1
            else:
                checked.bad.append(member.name)
    checked.missing = sorted(wanted)
    return checked


def report_checked(checked: Checked) -> bool:
    if checked.passed:
        done(f"Checksums match: {kinds_line(checked.ok)}")
        return True
    parts = [f"{len(checked.bad)} changed", f"{len(checked.missing)} missing"]
    if checked.unlisted:
        parts.append(f"{len(checked.unlisted)} not in the checksum list")
    if checked.unreadable_lines:
        parts.append(f"{checked.unreadable_lines} damaged checksum lines")
    fail(f"The backup doesn't match its checksums: {', '.join(parts)}")
    listing([(name, "doesn't match its checksum") for name in checked.bad]
            + [(name, "missing from the archive") for name in checked.missing]
            + [(name, "not in the checksum list") for name in checked.unlisted])
    return False


PAR2_PROGRESS = re.compile(rb"(Loading|Scanning|Constructing|Processing|Verifying|Repairing|Computing|Opening)"
                           rb"[^:\r\n]*:\s*(\d+(?:\.\d+)?)%")


def run_par2(args: list[str], cwd: Path, label: str) -> tuple[int, str]:
    """par2 with its own percentage driving the bar. It runs in a session of its own, so Ctrl-C reaches only us;
    we stop par2 and the caller cleans up after it."""
    try:
        process = subprocess.Popen(["par2", *args], cwd=cwd, stdin=subprocess.DEVNULL,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True)
    except FileNotFoundError:  # removed since the run started: the callers say so, as for any par2 failure
        return 127, "par2 isn't installed"
    output = bytearray()
    started = time.monotonic()

    def drain():
        while chunk := process.stdout.read1(4096):
            output.extend(chunk)

    reader = threading.Thread(target=drain, daemon=True)
    reader.start()
    try:
        with progress_bar() as bar:
            task = bar.add_task("", total=100, detail=label, note="")
            while process.poll() is None:
                found = PAR2_PROGRESS.findall(bytes(output[-4096:]))
                if found:
                    phase, percent = found[-1]
                    bar.update(task, completed=min(float(percent), 99.9), note=phase.decode().lower())
                time.sleep(0.2)
    except BaseException:
        process.terminate()
        try:
            process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait()
        raise
    reader.join(timeout=2)
    LOG.info("   par2 %s: exit %s after %.1fs", " ".join(args), process.returncode, time.monotonic() - started)
    return process.returncode, output.decode(errors="replace")


def remove_parity(archive: Path) -> None:
    """Delete an incomplete repair-data set, so it can't later pass for damage."""
    for path in archive.parent.glob(glob.escape(archive.name) + "*.par2"):
        path.unlink(missing_ok=True)


def check_parity(archive: Path, *, repair: bool) -> str:
    """'ok', 'repaired', 'damaged' (fixable, repair not asked for), 'failed' or 'skipped'. Only real damage counts
    against the backup. Unusable repair data is skipped: the checksums still decide."""
    parity = sidecar(archive, ".par2")
    if not parity.is_file():
        say("[hint]No repair data next to this backup.[/]")
        return "skipped"
    if not have_par2():
        warn(f"par2 isn't installed, so the repair data can't be used ({install_hint('par2')}).")
        return "skipped"
    code, output = run_par2(["verify", "--", parity.name], archive.parent, "checking repair data")
    if code == 0:
        done("Repair data says the backup is intact")
        return "ok"
    if code == 127:
        warn(f"par2 isn't installed any more, so the repair data can't be used ({install_hint('par2')}).")
        return "skipped"
    if re.search(rf'Target: "{re.escape(archive.name)}" - missing', output):
        warn("The repair data is for a file with another name, so it was skipped.")
        return "skipped"
    if code not in (1, 2):
        warn(f"The repair data itself is unreadable (par2 code {code}), so it was skipped. "
             "The checksums still check every file.")
        return "skipped"
    if code == 2:
        fail("The backup is damaged beyond what its repair data can fix.")
        return "failed"
    if not repair:
        warn("Repair data found damage it can fix. Restore repairs it before unpacking.")
        return "damaged"
    warn("Repair data found damage. Repairing…")
    # par2 moves each damaged file aside as <name>.1 and writes a repaired one in its place. Stopped or failed
    # partway, that new file is incomplete, so the damaged one, nearly all of it good, goes back.
    aside = [sidecar(path, ".1") for path in (archive, sidecar(archive, ".sha256"))]
    there = {path for path in aside if path.exists()}

    def put_back() -> None:
        for path in aside:
            if path.exists() and path not in there:
                os.replace(path, path.with_name(path.name.removesuffix(".1")))

    try:
        code, _ = run_par2(["repair", "--", parity.name], archive.parent, "repairing")
    except BaseException:
        put_back()
        raise
    if code == 0:
        for leftover in archive.parent.glob(glob.escape(archive.name) + "*.1"):  # par2 checked the repair already
            leftover.unlink(missing_ok=True)
        done("Repaired from the repair data")
        return "repaired"
    put_back()
    fail("Couldn't repair the backup.")
    return "failed"


def nearest_existing(path: Path) -> Path | None:
    for candidate in (path, *path.parents):
        if candidate.is_dir():
            return candidate
    return None


def free_space(path: Path) -> int:
    try:
        return shutil.disk_usage(nearest_existing(path) or path).free
    except OSError:
        return 0


def filesystem_of(path: Path) -> str:
    """The filesystem a path is on, e.g. apfs, msdos, exfat or vfat. diskutil only answers for a volume's own top
    folder, so walk up to it first."""
    mount = Path(os.path.realpath(nearest_existing(path) or path))
    while not os.path.ismount(mount):
        mount = mount.parent
    return _filesystem_at(str(mount))


@functools.cache  # asked on every keystroke in a path field
def _filesystem_at(mount: str) -> str:
    if IS_MAC:
        return (diskutil_info(mount).get("FilesystemType") or "").lower()
    return _mount_types().get(mount, "").lower()


def too_big_for(path: Path, size: int) -> str | None:
    """Why an archive of about `size` can't go in `path`, if it can't: FAT holds no file over 4 GB."""
    if size * 1.01 > FAT_MAX_FILE and filesystem_of(path) in FOUR_GB_FILESYSTEMS:
        return f"That drive is FAT, which can't hold a file over 4 GB, and this backup is about {human(size)}."
    return None



# ── Backup sets ───────────────────────────────────────────────────────────────
# Everything Restore can put books back from, each a folder with a .source.json naming the card or folder it came
# from: the books saved before a change (<date>/<card>/), Back up's whole-card archives (<date>/<card> (whole card)/,
# or the card's kept-current one, <card> (kept current)/, rebuilt in place), and the whole-card folder copies Back up
# made before it made archives.

WHOLE_CARD = " (whole card)"
KEPT = " (kept current)"


@dataclass
class BackupSet:
    date: str                       # the day it was made (kept current: last updated), as this computer reads it
    home: Path                      # its folder
    books: list[str]                # EPUBs, as paths on the card
    others: list[str]               # the other files the X4 opens
    archive: Path | None = None     # a whole-card archive; None for a folder of books
    digests: dict = field(default_factory=dict)  # NFC path on the card: checksum, from the archive's checksum list
    whole: bool = False             # a finished whole-card backup
    kept: bool = False              # the card's kept-current backup
    updated: str = ""               # when a kept-current backup was last updated, as stored
    unfinished: bool = False        # a whole-card folder copy that was stopped partway
    damaged: bool = False           # an archive whose checksum list is missing or damaged

    @property
    def files(self) -> list[str]:
        return self.books + self.others

    def hint(self, files: list[str]) -> str:
        """What it holds of `files`, for a list of backups."""
        if self.damaged:
            return "checksum list missing or damaged"
        return tally(sum(classify(rel) == "book" for rel in files), sum(classify(rel) == "other" for rel in files))


def newest_first(sets: list[BackupSet]) -> list[BackupSet]:
    """By day, then the later of two the same day ("(10)" after "(9)")."""
    return sorted(sets, key=lambda found: (found.date, found.kept, natural_key(found.home.name)), reverse=True)


def read_note(note: Path) -> dict | None:
    try:
        saved = json.loads(note.read_text())
    except (OSError, ValueError):
        return None
    return saved if isinstance(saved, dict) else None


def write_note(home: Path, saved: dict) -> None:
    """A set's .source.json, swapped in whole."""
    note = home / ".source.json"
    temp = note.with_name(".source.json.tmp")
    temp.write_text(json.dumps(saved, indent=2))
    temp.replace(note)


def archive_in(home: Path) -> Path | None:
    return next(iter(sorted(home.glob("*.tar.zst"))), None)


def archived_files(manifest: Path) -> dict[str, str] | None:
    """An archive's checksum list as NFC path on the card: checksum, for its books and other files (not the X4's
    records). None when it's missing, empty or damaged: then nothing can be told from it."""
    try:
        listed, unreadable = read_manifest(manifest)
    except OSError:
        return None
    if unreadable or not listed:
        return None
    return {rel: digest for name, digest in listed.items()
            if classify(rel := nfc(archived_rel(name))) in ("book", "other")
            and not rel.startswith("/") and "" not in rel.split("/")}  # never a path outside where it goes back


def read_set(note: Path) -> BackupSet | None:
    saved = read_note(note)
    if saved is None:
        return None
    home, kept = note.parent, saved.get("kept_current") is True
    date = (local_date(saved.get("updated")) or "unknown date") if kept else home.parent.name
    if archive := archive_in(home):
        digests = archived_files(sidecar(archive, ".sha256"))
        files = list(digests or {})
        return BackupSet(date, home, [rel for rel in files if classify(rel) == "book"],
                         [rel for rel in files if classify(rel) == "other"], archive, digests or {}, whole=True,
                         kept=kept, updated=str(saved.get("updated", "")), damaged=digests is None)
    files = list_books(home, kinds=tuple(RECORD_PREFIXES)) + sleep_images(home)
    return BackupSet(date, home, [rel for rel in files if classify(rel) == "book"],
                     [rel for rel in files if classify(rel) == "other"], whole=saved.get("whole_card") == "done",
                     unfinished=saved.get("whole_card") == "started")


def unchanged(earlier: Path, book: Path) -> bool:
    """A book in a folder set is the same as the one on the card, as far as size and modified time tell (as rsync
    judges it). FAT keeps local time, so a clock change shifts every file by exactly an hour; that still counts."""
    try:
        before, now = earlier.stat(), book.stat()
    except OSError:
        return False
    return before.st_size == now.st_size and abs(int(before.st_mtime) - int(now.st_mtime)) in (0, 3600)


def backup_sets(root: Path, card: Card | None, folder: Path) -> list[BackupSet]:
    """Every backup set in `folder` taken from this card or folder, newest first."""
    notes = [*folder.glob("*/.source.json"), *folder.glob("*/*/.source.json")]
    for note in notes:
        if (note.parent / ".new" / ".ready").exists():  # an update stopped while it moved in: finished first
            with suppress(OSError):
                settle_kept(note.parent)
    sets = [found for note in notes  # a hidden folder is never a set: .new is an update being built
            if not note.parent.name.startswith(".") and _same_source(note, root, card) and (found := read_set(note))]
    return newest_first(sets)


def whole_card_backups(folder: Path, card: Card) -> list[BackupSet]:
    """This card's finished whole-card backups in `folder`, newest first."""
    return [found for found in backup_sets(card.mount, card, folder) if found.whole]


def card_archives(card: Card) -> list[BackupSet]:
    """This card's whole-card archives, in the backups folder in use and the default one, newest first."""
    found = {s.archive: s for root in dict.fromkeys([RUN.backups, DEFAULT_BACKUPS])
             for s in backup_sets(card.mount, card, root) if s.archive}
    return newest_first(list(found.values()))


def find_kept(card: Card) -> BackupSet | None:
    """The card's kept-current backup, in the backups folder in use or the default one; the most recently updated,
    should there be two. A card without an ID has none: it could never be found again."""
    if not card.uuid:
        return None
    return max((found for found in card_archives(card) if found.kept), key=lambda found: found.updated, default=None)



# ── Task: back up the card ────────────────────────────────────────────────────
# A dated backup is never changed. A kept-current one is the one kind that's updated: rebuilt whole from the card each
# time, since one compressed file can't be patched. An update is packed, read back and given repair data in a hidden
# .new folder beside the old copy, under the final names (par2 records them), and moves in only once it checks out;
# .ready there says it did, so a move cut short is finished next time (settle_kept).

def ask_backup_kind(kept: BackupSet | None, card: Card):
    """A new dated backup, or the card's kept-current one: "dated", "kept" or BACK."""
    if not card.uuid:
        return "dated"  # without an ID, the card's kept-current backup could never be found again
    width = 28
    dated = option("New dated backup", "dated", "a folder of its own; older backups stay as they are", width=width)
    if kept:
        choices = [option(f"Update {kept.home.name}", "kept", f"last updated {kept.date}", width=width), dated]
    else:
        choices = [dated, option("Start a kept-current backup", "kept", "one backup you update after each change",
                                 width=width)]
    return ask_select("Into?", [*choices, back()])


def next_whole_card_set(folder: Path, card: Card) -> Path:
    """Where a new dated backup goes: today's set, or "(2)", "(3)" … after one the same day."""
    label = card.name + WHOLE_CARD
    home, number = folder / (RUN.day or today()) / label, 2
    while home.exists():
        home, number = home.with_name(f"{label} ({number})"), number + 1
    return home


def new_kept_folder(folder: Path, card: Card) -> Path:
    """Where a card's first kept-current backup goes: "<card> (kept current)", or "(2)" … when another card with the
    same name has that one."""
    label = card.name + KEPT
    home, number = folder / label, 2
    while home.exists():
        home, number = folder / f"{label} ({number})", number + 1
    return home


@dataclass
class BackupChanges:
    added: list[str] = field(default_factory=list)     # new since the backup
    dropped: list[str] = field(default_factory=list)   # the update drops these
    moved: int = 0                                      # somewhere else now, under the same name

    @property
    def removes(self) -> bool:
        return bool(self.dropped)


def compare_with_backup(before: dict[str, str], after: list[str], digest_of) -> BackupChanges:
    """What an update changes, from NFC paths and the backup's checksums. A book that's somewhere else now under the
    same name with the same contents, its folder moved or renamed, counts as moved: not as dropped and added. Two
    different books can share a name ("Poems.epub"), so `digest_of(path)`, a file's checksum on the card, is asked
    for each new path whose name the backup has elsewhere."""
    new = set(after)
    added, dropped = [rel for rel in after if rel not in before], [rel for rel in before if rel not in new]
    unmatched = {}  # file name: the dropped paths with it, not yet matched to a move
    for rel in dropped:
        unmatched.setdefault(posixpath.basename(rel), []).append(rel)
    changes, moved = BackupChanges(), set()
    for rel in added:
        twins = unmatched.get(posixpath.basename(rel))
        digest = digest_of(rel) if twins else None
        twin = next((old for old in twins if before[old] == digest), None) if digest else None
        if twin:
            twins.remove(twin)
            moved.add(twin)
        else:
            changes.added.append(rel)
    changes.dropped, changes.moved = [rel for rel in dropped if rel not in moved], len(moved)
    return changes


def show_backup_changes(changes: BackupChanges, limit: int = 6) -> None:
    if not (changes.added or changes.dropped or changes.moved):
        say("  [hint]Same books as the backup; it's rebuilt to pick up any changed contents.[/]")
        return
    for rel in changes.added[:limit]:
        say(f"  [accent]+[/] {esc(rel)}")
    for rel in changes.dropped[:limit]:
        say(f"  [bad]− {esc(rel)}[/]  [hint]dropped from the backup[/]")
    if hidden := max(0, len(changes.added) - limit) + max(0, len(changes.dropped) - limit):
        say(f"  [hint]… {hidden:,} more[/]")
    if changes.moved:
        say(f"  [hint]~ {changes.moved:,} moved or renamed[/]")
    if changes.dropped:
        warn("The update drops what's marked −. Afterwards it's only in older dated backups, if any.")


def discard(staging: Path, *, dated: bool) -> None:
    """A backup that was stopped or didn't check out goes, all of it: the card is still there to back up again.
    An update's .new goes; its old copy stays."""
    shutil.rmtree(staging, ignore_errors=True)
    if dated:
        with suppress(OSError):
            staging.parent.rmdir()  # the day's folder, only when it was new, so empty


def still_mounted(card: Card) -> bool:
    """Back up only reads the card. One without an ID can't be checked by it, so it just has to be still mounted."""
    return card_still_here(card) if card.uuid else os.path.ismount(card.mount)


def move_in(staging: Path, folder: Path) -> None:
    """Move a checked copy in place of the old one: its files first, then the old one's that they didn't replace.
    .ready in staging lists the copy's files and says it checked out, so a move cut short (a crash, a pulled drive)
    is finished by settle_kept next time."""
    new = set((staging / ".ready").read_text(encoding="utf-8", errors="replace").splitlines())
    for name in sorted(new):
        if (staging / name).exists():  # not moved in yet
            os.replace(staging / name, folder / name)
    # The old copy's files go only once every new one is in place. A list a crash cut short names too little, and
    # trusting it would delete the old copy and the new one with it.
    archive = next((name for name in new if name.endswith(".tar.zst")), None)
    whole = archive is not None and {f"{archive}.sha256", ".source.json"} <= new
    if not (whole and all((folder / name).exists() for name in new)):
        warn(f"An update of {esc(tilde(folder))} was cut short, so nothing of its old copy was deleted. "
             "Update it again to rebuild it.")
        (staging / ".ready").unlink(missing_ok=True)
        return
    for path in folder.iterdir():
        if path.name not in new and not path.name.startswith(".") and path.name.endswith(
                (".tar.zst", ".tar.zst.sha256", ".par2")):
            path.unlink(missing_ok=True)
    shutil.rmtree(staging, ignore_errors=True)


def settle_kept(folder: Path) -> None:
    """What a stopped update left in .new: a checked copy part-way moved in is moved the rest of the way; anything
    else there never checked out, and goes."""
    staging = folder / ".new"
    if (staging / ".ready").exists():
        warn("Finishing an update that was stopped while its new copy moved in.")
        move_in(staging, folder)
    shutil.rmtree(staging, ignore_errors=True)


def card_given(target: Path) -> Card:
    """The card a path on the command line names: the card itself, not a folder on it."""
    card = card_for(target)
    if card is None or card_rel(card, target):
        raise SafetyError('Give the card itself, like "/Volumes/XTEINK X4".')
    return card


def task_backup(opts: Options, state: dict):
    if target := path_arg(opts):
        card = card_given(target)
        show_card(card, state, chosen=True)
    elif (card := choose_card(state, changes=False)) is None:
        return BACK
    # every kind of file the X4 opens; a folder that can't be read would leave the backup short
    found = list_books(card.mount, kinds=tuple(RECORD_PREFIXES), strict=True) + sleep_images(card.mount, strict=True)
    if not found:
        fail("No books on the card.")
        outro("Nothing to back up.", good=False)
        return None
    books, others = [rel for rel in found if classify(rel) == "book"], [rel for rel in found if classify(rel) == "other"]
    members = found + device_record_paths(card.mount)
    total = sum((card.mount / rel).stat().st_size for rel in members)
    counted = tally(len(books), len(others))
    with doing("Backing up", card.name):
        say(f"[hint]{counted} · {human(total)}, with the X4's reading progress, bookmarks and recent list[/]")
        kept = find_kept(card)
        kind = ask_backup_kind(kept, card)
        if kind is BACK:
            return BACK
        updating = kind == "kept" and kept is not None
        chosen = None  # a backups folder picked here, remembered once the backup goes ahead
        if updating:
            folder = kept.home
            if problem := too_big_for(folder, total):
                fail(problem)
                outro("Nothing was written.", good=False)
                return None
        else:
            chosen = ask_backups_folder(card.mount, size=total)
            if chosen is BACK:
                return BACK
            folder = new_kept_folder(chosen, card) if kind == "kept" else next_whole_card_set(chosen, card)

        with_parity = PARITY_PERCENT > 0 and have_par2()
        before = kept.digests if updating and not kept.damaged else None
        listed = {nfc(rel): rel for rel in found}

        def digest_of(rel: str) -> str | None:
            try:
                return _digest(card.mount / listed[rel]).hex()
            except OSError:
                return None  # unreadable: not counted as a move, so it shows as dropped and added

        changes = compare_with_backup(before, list(listed), digest_of) if before is not None else None
        if updating:
            say(f"Updates  [strong]{esc(tilde(folder))}/[/]  [hint]last updated {kept.date}[/]")
            if changes is None:
                warn("Its checksum list is missing or damaged, so what this update would drop can't be told.")
            else:
                show_backup_changes(changes)
        else:
            holds = "the archive, its checksums" + (" and repair data" if with_parity else "")
            say(f"Creates  [strong]{esc(tilde(folder))}/[/]  [hint]{holds}"
                + ("; kept current, so later backups update it" if kind == "kept" else "") + "[/]")
        if not with_parity and PARITY_PERCENT > 0:
            say(f"  [hint]No repair data: par2 isn't installed ({install_hint('par2')}).[/]")
        needed = int(total * (1 + (PARITY_PERCENT / 100 if with_parity else 0)))
        room = free_space(folder)
        say(f"[hint]Needs about {human(needed)}, {human(room)} free there"
            + (", while the old copy stays until the new one checks out" if updating else "") + "[/]")
        if opts.dry_run:
            outro("Preview only. Nothing was written, and the backups folder is as it was.")
            return None
        if needed > room and not ask_confirm("Not enough room there. Start anyway?", False):
            outro("Nothing was written.", good=False)
            return None
        removes = updating and (changes is None or changes.removes)  # not known counts as dropping
        if ask_go(f"Update {folder.name}" if updating else f"Back up {counted}", state, card.mount, saves=False,
                  safe=removes) is BACK:
            return BACK
        if chosen:
            use_backups_folder(state, chosen)
        if updating:
            settle_kept(folder)

        good = write_backup(card, members, folder, kind=kind, updating=updating, before=before, counted=counted,
                            with_parity=with_parity, total=total)
        os.sync()
        if good and card.uuid:  # for the menu's reminder, which a card without an ID doesn't get
            state.setdefault("cards", {}).setdefault(card.uuid, {"name": card.name})["backed_up"] = \
                datetime.now(UTC).isoformat(timespec="seconds")
            save_state(state)
        if good:
            done(f"Backup {'updated' if updating else 'saved'} in {esc(tilde(folder))}")
            if once("second copy"):
                say("[hint]Keep a second copy somewhere else, like another drive.[/]")
    finish_card(card, state, changed=False)
    return None


def write_backup(card: Card, members: list[str], folder: Path, *, kind: str, updating: bool,
                 before: dict[str, str] | None, counted: str, with_parity: bool, total: int) -> bool:
    """Pack the card, read it back from the drive, then give it its final names and repair data. True when the
    backup is in place and checked out. Anything stopped or failed before that is deleted. A new backup is built in
    its own new folder; an update, in .new beside the old copy, which stays until the new one has moved in."""
    staging = folder / ".new" if updating else folder
    name = f"{card.name}.tar.zst"
    archive, manifest = staging / name, staging / f"{name}.sha256"
    part, sums = sidecar(archive, PARTIAL), sidecar(manifest, PARTIAL)
    if not still_mounted(card):  # still the card that was listed
        raise SafetyError(f"{card.mount} is no longer the card you picked ({card.name}).")
    staging.mkdir(parents=True)
    dated = kind == "dated"
    try:
        with progress_bar() as bar:
            task = bar.add_task("", total=max(total, 1), detail="packing", note=f"zstd level {ZSTD_LEVEL}")
            skipped = write_archive([(f"{card.name}/{rel}", card.mount / rel) for rel in members], part, sums,
                                    lambda n: bar.advance(task, n))
        if not still_mounted(card):
            fail(f"{esc(card.name)} was swapped or unmounted while it was being packed, so nothing was kept.")
            discard(staging, dated=dated)
            return False
        done(f"Packed {counted} into {esc(name)} ({human(part.stat().st_size)})")
        if skipped:
            warn(f"{plural(skipped, 'file')} with a line break in the name can't be in the checksum list, so "
                 "Restore can't put them back. They're in the archive, and tar -xf unpacks them.")

        # books the kept-current backup has, rewritten since: opened from the new copy before it replaces theirs
        new = archived_files(sums) or {}
        inspect = {nfc(card.name) + "/" + rel for rel, digest in new.items()
                   if before and classify(rel) == "book" and before.get(rel, digest) != digest}
        try:
            with progress_bar() as bar:
                task = bar.add_task("", total=part.stat().st_size, detail="reading it back", note="")
                checked = verify_archive(part, sums, lambda n: bar.advance(task, n), inspect=inspect)
        except READ_ERRORS as error:
            fail(f"The backup didn't read back: {esc(str(error))}")
            checked = None
        if checked is None or not report_checked(checked):
            discard(staging, dated=dated)
            warn(("Nothing was kept, and the kept-current backup stays as it was." if updating else "Nothing was kept.")
                 + " Try another drive.")
            return False
        if checked.damaged_books:
            warn(f"{plural(len(checked.damaged_books), 'book')} changed since the backup and won't open now:")
            listing([(archived_rel(name), esc(why)) for name, why in checked.damaged_books])
            say("[hint]The backup's copies are as they were. Check books can test the card's.[/]")
            if not ask_confirm("Replace the backup's copies with these anyway?", False):
                discard(staging, dated=dated)
                say("[hint]The kept-current backup stays as it was.[/]")
                return False
        os.replace(part, archive)
        os.replace(sums, manifest)
    except BaseException as error:
        discard(staging, dated=dated)
        if not isinstance(error, OSError):
            raise
        # A full or unplugged drive ends this backup, not the run: the card is as it was
        reading = bool(error.filename) and _under(Path(error.filename), card.mount)
        what = "The card couldn't be read" if reading else "The backup couldn't be written"
        fail(f"{what}: {esc(error.strerror or str(error))}"
             + (f" ({esc(tilde(error.filename))})" if error.filename else ""))
        say("[hint]" + ("The kept-current backup stays as it was. " if updating else "")
            + ("Check books can test the card." if reading else "Free up room, or back up to another drive.") + "[/]")
        return False

    source = {"path": str(card.mount), "card_uuid": card.uuid}
    kept_note = lambda: source | {"kept_current": True, "updated": datetime.now(UTC).isoformat(timespec="seconds")}
    if not updating:  # Restore, Check and Stats find it from here on
        try:
            write_note(folder, (source | {"whole_card": "done"}) if dated else kept_note())
        except OSError as error:
            discard(staging, dated=dated)
            fail(f"The backup couldn't be written: {esc(error.strerror or str(error))}")
            say("[hint]Free up room, or back up to another drive.[/]")
            return False
    if with_parity:
        try:
            code, _ = run_par2(["create", f"-r{PARITY_PERCENT}", "--", f"{name}.par2", name, manifest.name], staging,
                               "building repair data")
        except BaseException:
            remove_parity(archive)
            if updating:
                discard(staging, dated=False)
            else:
                warn("Stopped while building repair data. The backup is kept, checked, without repair data.")
            raise
        if code == 0:
            done(f"Repair data written, {PARITY_PERCENT}%")
        else:
            remove_parity(archive)
            warn("par2 couldn't build repair data, so none was kept. The backup and checksums are fine without it.")
    if updating:
        try:
            with ctrl_c_shield():  # a stop now would leave half of each copy
                write_note(staging, kept_note())  # moves in with the copy
                os.sync()  # the note and repair data too, before the list says the copy is complete
                names = "\n".join(sorted(path.name for path in staging.iterdir()))
                with open(staging / ".ready", "w", encoding="utf-8") as ready:  # on the drive before anything moves
                    ready.write(names)
                    durable(ready)
                move_in(staging, folder)
        except OSError as error:
            fail(f"The new copy couldn't be moved in: {esc(error.strerror or str(error))}")
            say("[hint]Run Back up again to finish the update.[/]")
            return False
    return True


def backup_reminder(state: dict, card: Card) -> str | None:
    """A line saying a card has changed since its last whole-card backup, if this script changed it since. Changes made
    elsewhere (in Finder, or the device's own records) aren't known."""
    entry = state.get("cards", {}).get(card.uuid, {}) if card.uuid else {}
    changed, backed_up = remembered_time(entry.get("updated")), remembered_time(entry.get("backed_up"))
    if changed and backed_up and changed > backed_up:
        return (f"{esc(card.name)} has changed since it was last backed up, "
                f"{backed_up.astimezone().date().isoformat()}. Back up saves a new whole-card backup.")
    if changed and not backed_up:
        return f"{esc(card.name)} has changed, and has no whole-card backup yet. Back up saves one."
    return None


def backup_reminders(state: dict) -> list[str]:
    """The reminder for each card plugged in, for the menu."""
    return [note for card in list_cards() if (note := backup_reminder(state, card))]


def remembered_time(stamp) -> datetime | None:
    """A time from the state file, or None when it isn't one (a hand-edited file)."""
    try:
        when = datetime.fromisoformat(stamp)
    except (TypeError, ValueError):
        return None
    return when if when.tzinfo else None  # every time written here has a zone; one without can't be compared


def local_date(stamp) -> str | None:
    """A remembered time as this computer's date, or None when it isn't one."""
    when = remembered_time(stamp)
    return when.astimezone().date().isoformat() if when else None



# ── Task: restore ─────────────────────────────────────────────────────────────

REAL_DAMAGE = ("listed but missing", "reading order names a missing")


def check_book(raw: bytes) -> tuple[str | None, bool]:
    """(why a book won't read properly, or None; whether it has harmless quirks). Damage stops a book
    opening or leaves part of it out. A broken contents link or a publisher image the book never
    shipped is only a quirk: plenty of books that read fine have them."""
    try:
        with zipfile.ZipFile(io.BytesIO(raw)) as archive:
            if damaged := archive.testzip():
                return f"a file inside is damaged: {damaged}", False
        entries = read_epub(raw)
    except BAD_ZIP:
        return "won't open: not a readable EPUB", False
    problems = structure_problems(entries)
    damage = next((p for p in problems if p.startswith(("no package document", *REAL_DAMAGE))), None)
    return damage, damage is None and bool(problems)


def extract_files(backup: BackupSet, rels: list[str], into: Path) -> tuple[dict[str, Path], list[tuple[str, str]]]:
    """The picked files out of a whole-card archive into `into`, in one pass, each compared with its checksum:
    ({NFC path: its copy}, [(path, why) for each left out])."""
    wanted, found, problems = {nfc(rel): rel for rel in rels}, {}, []
    with progress_bar() as bar:
        task = bar.add_task("", total=backup.archive.stat().st_size, detail="reading the backup", note="")
        with open_archive(backup.archive, lambda n: bar.advance(task, n)) as tar:
            for member in tar:
                key = nfc(archived_rel(member.name))
                if key not in wanted or key in found or not member.isfile():
                    continue
                data = tar.extractfile(member).read()
                if hashlib.sha256(data).hexdigest() != backup.digests.get(key):
                    problems.append((wanted.pop(key), "the backup's copy doesn't match its checksum"))
                    continue
                copy = into / f"{len(found)}{posixpath.splitext(key)[1]}"
                copy.write_bytes(data)
                found[key] = copy
    problems += [(rel, "not in the backup") for key, rel in wanted.items() if key not in found]
    return found, problems


def read_from_archive(backup: BackupSet, rels: list[str], into: Path, *, repair: bool) -> list[tuple[str, Path]] | None:
    """The picked files out of a whole-card archive, each checked against its checksum; one that doesn't match, or
    isn't there, is named and left out. Either, or an archive that can't be read, has its repair data tried once
    (only checked, with `repair` False, as in a dry run). None when it can't be read at all."""
    for attempt in (1, 2):
        error = None
        try:
            found, problems = extract_files(backup, rels, into)
        except READ_ERRORS as caught:
            found, problems, error = {}, [], caught
        if not (problems or error) or attempt == 2 or check_parity(backup.archive, repair=repair) != "repaired":
            break
        backup = read_set(backup.home / ".source.json") or backup  # the checksum list may have been repaired too
    if error:
        fail(f"The backup couldn't be read: {esc(str(error))}")
        return None
    for rel, why in problems:
        mark_failed()
        say(f"  [bad]✗[/] {esc(rel)}")
        say(f"      [hint]{why}; left out[/]")
    return [(rel, found[nfc(rel)]) for rel in rels if nfc(rel) in found]


def repaired_set(backup: BackupSet, *, repair: bool) -> BackupSet | None:
    """A whole-card archive whose checksum list is missing or damaged, put right from its repair data if it can be
    (only checked, with `repair` False, as in a dry run)."""
    if check_parity(backup.archive, repair=repair) == "repaired":
        fixed = read_set(backup.home / ".source.json")
        if fixed and not fixed.damaged:
            return fixed
    fail("Its checksum list is missing or damaged, so its books can't be checked.")
    return None


def task_restore(opts: Options, state: dict):
    if target := path_arg(opts):
        if _under(target, RUN.backups):
            raise SafetyError("Give the card or folder to restore into. Restore finds its backups itself.")
        card, root, start = locate(target)
        if card:
            show_card(card, state, chosen=True)
    else:
        if (card := choose_card(state)) is None:
            return BACK
        root, start = card.mount, ""

    def wanted(rel: str) -> bool:
        return not start or nfc(rel) == nfc(start) or nfc(rel).startswith(nfc(start) + "/")

    elsewhere, folder = object(), RUN.backups
    while True:  # the backups folder in use, or another one the backups were saved in before
        sets = [(found, files) for found in backup_sets(root, card, folder)
                if (files := [rel for rel in found.files if wanted(rel)]) or found.damaged]
        if not sets:
            say(f"[hint]No backups of {'this card' if card else 'this folder'} in {esc(tilde(folder))}.[/]")
        choices = [option(found.date, found, f"{found.home.name} · {found.hint(files)}"
                          + (" · unfinished" if found.unfinished else ""), width=15)
                   for found, files in sets]
        choices += [divider()] if choices else []
        choices += [action_choice("Look in another folder…", elsewhere, "→"), back()]
        source = ask_select("Restore from?", choices)
        if source is BACK:
            return BACK
        if source is not elsewhere:
            break
        places = [] if folder == DEFAULT_BACKUPS else [(tilde(DEFAULT_BACKUPS) + "/", "the default, beside the script")]
        places += [(str(c.mount) + "/", c.kind) for c in list_cards() if not _under(root, c.mount)]
        if (picked := ask_path("Look for backups in?", "", places, books=False)) is not BACK:
            folder = picked
    with doing("Restoring from", f"{source.date} · {source.home.name}"), \
            tempfile.TemporaryDirectory(prefix="xteink-") as staging:
        if source.damaged and (source := repaired_set(source, repair=not opts.dry_run)) is None:
            outro("Nothing was restored.", good=False)
            return None
        pairs = [(rel, source.home / rel) for rel in source.files if wanted(rel)]
        picked = ask_checkbox("Which books?", [Choice(title=rel, value=(rel, path)) for rel, path in pairs])
        if picked is BACK:
            return BACK
        if source.archive:  # read out and checked before anything is planned
            picked = read_from_archive(source, [rel for rel, _ in picked], Path(staging), repair=not opts.dry_run)
            if picked is None:
                outro("Nothing was restored.", good=False)
                return None

        jobs = []
        for rel, path in picked:
            if is_book_name(rel) and (damage := check_book(path.read_bytes())[0]):
                mark_failed()
                say(f"  [bad]✗[/] {esc(rel)}")
                say(f"      [hint]the backup is damaged ({esc(damage)}); left out[/]")
                continue
            job = Job(rel, path)
            set_destination(root, job, rel)
            if job.same:
                say(f"  [hint]= {esc(job.dest)}: the copy there now is exactly the same; skipped[/]")
                continue
            jobs.append(job)
            say(f"  [accent]↺[/] {esc(job.dest)}")
            details = ["replaces the current copy" if job.replaces else "puts it back"]
            if job.replaces and (note := progress_note(card, job.dest, job.keep_progress)):
                details.append(note)
            say(f"      [hint]{' · '.join(details)}[/]")
        if not jobs:
            outro("Nothing to restore.")
            return None
        if any(job.replaces for job in jobs):
            backup_line(opts, "Current copies")
        elif card:
            backup_line(opts, "The X4's reading progress and bookmarks", always=True)
        if opts.dry_run:
            outro("Preview only. Nothing was restored.")
            return None
        saves = card is not None or (opts.backup and any(job.replaces for job in jobs))
        counted = tally(sum(is_book_name(job.dest) for job in jobs), sum(not is_book_name(job.dest) for job in jobs))
        if ask_go(f"Restore {counted}", state, root, cancel="No", safe=True, saves=saves) is BACK:
            outro("Nothing changed.")
            return None

        records = begin_card_changes(card, state) if card else None
        label = card.name if card else root.name
        for job in batch(jobs, "restored", lambda job: job.dest):
            put_book(root, job.dest, job.source.read_bytes(), card=card, records=records, label=label,
                     backup=opts.backup, keep_progress=job.keep_progress)
        done(f"Restored {counted}")
        receipt = Receipt()
        for job in jobs:
            receipt.add("↻" if job.replaces else "+", job.dest, "replaced" if job.replaces else "put back")
        finish_card(card, state, changed=True, receipt=receipt, folder=root)
        return None



# ── Task: check books ─────────────────────────────────────────────────────────

def ask_check_what(card: Card) -> str | Path | None:
    """The whole card (""), or one book or every book in a folder on it, picked as Move and Remove pick them, or one
    of its whole-card archives (the archive's Path). None to go back."""
    whole, some, backup = object(), object(), object()
    books = RUN.active[1] if RUN.active and RUN.active[0].uuid == card.uuid else len(list_books(card.mount))
    width = max(len(f"All of {card.name}"), len("One book, or a folder…"))
    while True:
        picked = ask_select("Check what?", [option(f"All of {card.name}", whole, plural(books, "book"), width=width),
                                            option("One book, or a folder…", some, "picked on the card", width=width),
                                            option("A backup of it…", backup, "every file in an archive, read and checked",
                                                   width=width),
                                            back()])
        if picked is BACK or picked is whole:
            return None if picked is BACK else ""
        if picked is some and (rel := ask_card_path(card, "Check which book or folder?", want="either")):
            return rel
        if picked is backup and (archive := ask_backup_archive(card)):
            return archive


def ask_backup_archive(card: Card) -> Path | None:
    """One of the card's whole-card archives, in the backups folder in use or the default one. None to go back."""
    sets = card_archives(card)
    if not sets:
        say(f"[hint]No whole-card archives of {esc(card.name)} in {esc(tilde(RUN.backups))}. Back up makes one.[/]")
        return None
    picked = ask_select("Which backup?", [*(option(found.date, found.archive, f"{found.home.name} · "
                                                   f"{human(found.archive.stat().st_size)}", width=15) for found in sets),
                                          back()])
    return None if picked is BACK else picked


def verify_backup(archive: Path) -> None:
    """Check a whole-card archive: its repair data, then every file in it read and compared with its checksum,
    unpacking nothing. Changes nothing."""
    with doing("Checking", archive.name):
        manifest = sidecar(archive, ".sha256")
        parity = check_parity(archive, repair=False)
        if not manifest.is_file():
            warn("No checksum list next to the backup. Testing that it unpacks cleanly instead.")
        try:
            with progress_bar() as bar:
                task = bar.add_task("", total=archive.stat().st_size, detail="reading every file", note="")
                checked = verify_archive(archive, manifest if manifest.is_file() else None,
                                         lambda n: bar.advance(task, n))
        except READ_ERRORS as error:
            fail(f"The backup is damaged: {esc(str(error))}")
            return
        if manifest.is_file():
            good = report_checked(checked)
        else:
            good = False
            done(f"Unpacks cleanly: {kinds_line(checked.seen)}")
            warn("Restore can't use a backup without its checksum list. tar -xf still unpacks it.")
        if good and parity in ("ok", "skipped"):
            done("The backup is good.")
        else:
            fail("The backup has problems. See above.")


def task_check(opts: Options, state: dict):
    if target := path_arg(opts):
        if target.is_file() and target.name.endswith(".tar.zst"):
            verify_backup(target)
            finish_card(None, state, changed=False)
            return None
        card, root, start = locate(target, backups_ok=True, changes=False)
        if card:
            show_card(card, state, chosen=True)
    else:
        card = choose_card(state, changes=False)
        if card is None:
            return BACK
        root, start = card.mount, ask_check_what(card)
        if start is None:
            return BACK
        if isinstance(start, Path):
            verify_backup(start)
            finish_card(card, state, changed=False)
            return None
    books = list_books(root, start)
    if not books:
        fail("No .epub books there.")
        outro("Nothing to check.", good=False)
        return None

    damaged, quirky, digests = [], 0, {}
    for rel in batch(books, "checked", shielded=False):
        raw = None
        try:
            raw = (root / rel).read_bytes()
            damage, quirks = check_book(raw)
        except OSError as error:  # on a failing card, this is the damage worth knowing about
            damage, quirks = f"couldn't be read ({error.strerror or error})", False
        if damage:
            damaged.append((rel, damage))
            digests[nfc(rel)] = hashlib.sha256(raw).hexdigest() if raw is not None else None
        quirky += quirks

    where = f" in {short(start)}" if start and not is_book_name(start) else ""
    if damaged:
        fail(f"{plural(len(damaged), 'book')} of {len(books):,}{esc(where)} won't read properly")
        # a copy as damaged as the book (the same bytes, as far as a backup can tell) won't help
        saved = {nfc(rel) for found in backup_sets(root, card, RUN.backups) for rel in found.files if nfc(rel) in digests
                 and (found.digests.get(nfc(rel)) != digests[nfc(rel)] if found.archive
                      else not unchanged(found.home / rel, root / rel))}
        listing([(rel, esc(why) + ("; Restore can put back a saved copy" if nfc(rel) in saved else ""))
                 for rel, why in damaged])
    else:
        done(f"{plural(len(books), 'book')} checked{esc(where)}, none damaged")
    if quirky:
        say(f"[hint]{plural(quirky, 'book')} {'has' if quirky == 1 else 'have'} harmless quirks, like a missing publisher "
            "image or a broken contents link. They read fine.[/]")
    finish_card(card, state, changed=False)
    return None



# ── Task: stats ───────────────────────────────────────────────────────────────
# The library at a glance, from what's quick to read: the card's file list and sizes, the folder names and
# the X4's own records. No book is opened, so it takes a moment even with a thousand of them.

def meter(part: float, whole: float, width: int = 20) -> Text:
    filled = min(width, round(width * part / whole)) if whole else 0
    return Text.assemble(("█" * filled, "accent"), ("░" * (width - filled), "rail"))


def stat_row(label: str, value: str | Text, width: int = 18) -> None:
    say(Text.assemble("  " + label.ljust(width), value if isinstance(value, Text) else Text.from_markup(value)))


def author_counts(books: list[str]) -> Counter:
    """Books per author: the folders named Last, First under a genre, matched as Add matches them (accents, case and
    spacing aside, so one author spelled two ways in two genres counts once), each shown as first spelled."""
    spelled, counts = {}, Counter()
    for parts in (rel.split("/") for rel in books):
        if len(parts) > 2 and ", " in parts[1]:
            key = fold(parts[1])
            spelled.setdefault(key, nfc(parts[1]))
            counts[key] += 1
    return Counter({spelled[key]: count for key, count in counts.items()})


def show_stats(card: Card, books: list[str], state: dict) -> None:
    root = card.mount
    sizes = {rel: (root / rel).stat().st_size for rel in books}
    genres = Counter(rel.split("/")[0] if "/" in rel else "(top level)" for rel in books)  # a bar each
    authors = author_counts(books)
    used = card.size - card.free

    say(f"[strong]{plural(len(books), 'book')}[/] · [strong]{plural(len(authors), 'author')}[/] · "
        f"[strong]{plural(len(top_folders(books)), 'genre')}[/] · {human(sum(sizes.values()))}")
    say(Text.assemble("Card  ", meter(used, card.size), f"  {human(used)} of {human(card.size)}"))
    say()
    say("[heading]Books per genre[/]")
    width = min(24, max(len(name) for name in genres))
    shown = genres.most_common(10)
    digits = len(f"{shown[0][1]:,}")
    for name, count in shown:
        say(Text.assemble("  " + short(name, width).ljust(width) + "  ", meter(count, shown[0][1], 16),
                          f"  {count:>{digits},}"))
    if len(genres) > len(shown):
        say(f"[hint]  … and {plural(len(genres) - len(shown), 'more genre')}[/]")

    device = root / DEVICE_DIR
    try:
        records = {entry.name for entry in os.scandir(device)}
    except OSError:
        records = None  # a card that hasn't been in an X4 yet
    if records is not None:
        marks = {}
        with suppress(OSError):  # the folder appears with the first bookmark
            marks = {nfc(entry.name): Path(entry.path) for entry in os.scandir(device / "bookmarks")}  # listed NFD
        opened = sum(cache_dir(root, rel).name in records for rel in books)
        marked = [marks[name] for rel in books if (name := bookmark_file(root, rel).name) in marks]
        bookmarks = 0
        for path in marked:
            with suppress(OSError, ValueError):
                saved = json.loads(path.read_text(encoding="utf-8"))
                bookmarks += len(saved) if isinstance(saved, list) else 0
        recent = [book.get("title") if isinstance(book.get("title"), str) else posixpath.basename(book["path"])
                  for book in DeviceRecords(root).recent_books()[:3]]
        say()
        say("[heading]Reading, from the X4's own records[/]")
        stat_row("Opened on the X4", f"{plural(opened, 'book')}  [hint]{opened * 100 // len(books)}% of the library[/]")
        stat_row("With bookmarks", f"{plural(len(marked), 'book')}, {plural(bookmarks, 'bookmark')}")
        if recent:
            stat_row("Recently read", " · ".join(esc(short(title, 30)) for title in recent))

    say()
    if authors:
        stat_row("Most books by", " · ".join(f"{esc(name)} {count}" for name, count in authors.most_common(3)))
    largest = max(books, key=sizes.get)
    stat_row("Largest book", f"{esc(short(posixpath.basename(largest), 40))}  [hint]{human(sizes[largest])}[/]")
    backups = whole_card_backups(RUN.backups, card)
    stat_row("Last backup", f"{backups[0].date}, {'kept current' if backups[0].kept else 'whole card'} · "
             f"{plural(len(backups), 'backup')} in {esc(tilde(RUN.backups))}" if backups
             else "[warn]no whole-card backup yet[/]")
    if reminder := backup_reminder(state, card):
        warn(reminder)


def task_stats(opts: Options, state: dict):
    if target := path_arg(opts):
        card = card_given(target)
    elif (card := choose_card(state, changes=False)) is None:
        return BACK
    books = list_books(card.mount)
    if not books:
        fail("No .epub books on the card.")
        outro("Nothing to show.", good=False)
        return None
    show_stats(card, books, state)
    outro("Done.")
    return None


# ── Help, menu and the command line ───────────────────────────────────────────

TASKS = [
    ("Add books", "add", "prepare new books and copy them onto the card"),
    ("Move or rename", "move", "books or folders; progress and bookmarks follow"),
    ("Remove books", "remove", "take books off; a copy is saved first"),
    ("Prepare books", "prepare", "clean and optimize, on the card or a folder"),
    ("Back up", "backup-card", "the whole card, into a checked archive"),
    ("Restore", "restore", "put books back from a backup"),
    ("Check books", "check", "find books that won't open, or check a backup"),
    ("Stats", "stats", "the library at a glance, and what you've read"),
]


# The menu, by what a task does: change the card, back it up, or tell you about it. Help, Settings and Quit
# sit below a line.
MENU_GROUPS = (("On the card", ("add", "move", "remove", "prepare")), ("Backups", ("backup-card", "restore")),
               ("Info", ("check", "stats")))

TAGLINE = "Manage the XTEINK X4's SD card and prepare books for it"
ABOUT = ("Add, move, rename and remove books on the X4's card, preparing them for its screen on the way. "
         "Reading progress follows every change, and books are backed up before they change.")


@dataclass(frozen=True)
class HelpPage:
    title: str
    hint: str            # its line in the list of topics
    about: str           # what it's for, in a sentence or three
    sections: tuple = ()  # (label, rows); a row is (left, right) in two columns, or a line of text


DRY_RUN = ("-n, --dry-run", "show what would change, change nothing")
YES = ("-y, --yes", 'skip "Go ahead?" in Add and Prepare')
PREPARE_OPTIONS = (("-f, --force", "optimize again books already optimized"),
                   ("-q, --quality N", "JPEG quality, 1-100 (85, as the firmware)"),
                   ("--keep-fonts, --keep-comments", "leave those in"))

HELP_PAGES = {  # one per task, in menu order
    "add": HelpPage(
        "Add books", "",
        "Copies books from this computer onto the card, prepared for the X4 on the way. Each is named from its own "
        "details, as [ Genre ]/Last, First/Title.epub; you pick the genre folder. You see where every book goes "
        "before anything is copied.",
        (("Run directly", ((f"{PROG} --add", "pick the card and the books as you go"),
                           (f"{PROG} --add ~/Downloads", "add the books in that folder, or one .epub"))),
         ("Options", (DRY_RUN, YES, ("--no-backup", "don't save the books it replaces"), *PREPARE_OPTIONS)),
         ("Good to know", (("A book that would replace a different book with the same name is flagged, and so "
                            "is a new genre folder."),
                           "Garbled characters in names, like H｣rin, are repaired.")))),
    "move": HelpPage(
        "Move or rename", "",
        "Renames a book or folder where it is, or moves it to another folder. Reading progress, bookmarks and the "
        "recent list go with it.",
        (("Run directly", ((f"{PROG} --move", "pick the card and the book as you go"),
                           (f'{PROG} --move "/Volumes/XTEINK X4/…/Dune.epub"', "start from that book or folder"))),
         ("Options", (DRY_RUN,)),
         ("Good to know", ("Move and rename books here, not in Finder, or their progress is lost.",)))),
    "remove": HelpPage(
        "Remove books", "",
        "Takes books off the card along with their progress, bookmarks and cache. A copy of each is saved first, "
        "so Restore can put it back.",
        (("Run directly", ((f"{PROG} --remove", "pick the card and the books as you go"),
                           (f'{PROG} --remove "/Volumes/XTEINK X4/…/Dune.epub"', "start from that book or folder"))),
         ("Options", (DRY_RUN, ("--no-backup", "don't keep a copy"))),
         ("Good to know", ("It always asks first, and Enter alone answers No.",)))),
    "prepare": HelpPage(
        "Prepare books", "",
        'Optimize does what CrossPoint\'s own "Optimize EPUB" does: grayscale JPEGs sized for the 480×800 screen, '
        "no embedded fonts. Clean repairs the books archive.org makes from page scans. Every book is checked before "
        "it replaces the original.",
        (("Run directly", ((f"{PROG} --prepare", "pick the card or a folder as you go"),
                           (f'{PROG} --optimize "/Volumes/XTEINK X4"', "optimize only, the whole card"),
                           (f"{PROG} --clean ~/Downloads --yes", "clean only; runs without a terminal"))),
         ("Options", (DRY_RUN, YES, ("--no-backup", "don't save the originals"), *PREPARE_OPTIONS)),
         ("Good to know", ("Clean only runs on archive.org scans: on a well-made book it would do harm.",
                           "Books already optimized are skipped.")))),
    "backup-card": HelpPage(
        "Back up", "",
        "Packs every book on the card, the other files it opens (TXT, MD, XTC and sleep-screen pictures), and the X4's "
        "reading progress, bookmarks and recent list into one archive with a checksum for each file, reads it back from the drive to "
        "check every file, then adds repair data.",
        (("Run directly", ((f"{PROG} --backup-card", "pick the card as you go"),
                           (f'{PROG} --backup-card "/Volumes/XTEINK X4"', "back up that card"))),
         ("Options", (DRY_RUN,)),
         ("Saved in", ((f"<date>/<card>{WHOLE_CARD}/", "a new dated backup; older ones stay as they are"),
                       (f"<card>{KEPT}/", "or one backup per card that each Back up updates"),
                       ("<card>.tar.zst", "the archive: a standard tar, compressed with zstd"),
                       ("<card>.tar.zst.sha256", "a checksum for every file in it"),
                       ("<card>.tar.zst*.par2", "repair data, when par2 is installed"))),
         ("Good to know", (("A kept-current backup is rebuilt whole each time. The old copy stays until the new one "
                            "checks out, and a book that changed since and won't open is shown first."),
                           ("A backup stopped partway, or one that doesn't read back cleanly, is deleted. The card is "
                            "still there to back up again."),
                           ('"Save the backup where?" starts at the backups folder in use. Another folder is used '
                            "for every backup from then on, once the backup goes ahead."),
                           ("The X4's fonts and caches aren't in it. The menu says when this script has changed the "
                            "card since its last backup; changes made in Finder aren't known."))))),
    "restore": HelpPage(
        "Restore", "",
        "Puts books back from a whole-card backup, or from the copies saved before books changed or were removed. "
        "Each book from an archive is checked against its checksum before anything is written.",
        (("Run directly", ((f"{PROG} --restore", "pick the card and a backup as you go"),
                           (f"{PROG} --restore ~/Books", "restore into that folder"))),
         ("Options", (DRY_RUN, ("--no-backup", "don't save the books it replaces"))),)),
    "check": HelpPage(
        "Check books", "",
        "Reads every book on the card, or one book or folder, and lists the ones that won't open or are missing "
        "parts, and says when Restore has a saved copy. Or reads every file in one of the card's backups and "
        "compares it with its checksum. It changes nothing.",
        (("Run directly", ((f"{PROG} --check", "pick the card, then all of it, a book, a folder or a backup"),
                           (f'{PROG} --check "/Volumes/XTEINK X4"', "check that card; runs without a terminal"),
                           (f"{PROG} --check …/XTEINK X4.tar.zst", "check that backup"))),
         ("Good to know", ("Harmless quirks, like a missing publisher image, are only counted.",)))),
    "stats": HelpPage(
        "Stats", "",
        "The library at a glance: books, authors and genres, how full the card is, which books have been opened "
        "on the X4 and bookmarked, and the last backup. No book is opened, so it's quick.",
        (("Run directly", ((f"{PROG} --stats", "pick the card as you go"),
                           (f'{PROG} --stats "/Volumes/XTEINK X4"', "that card; runs without a terminal"))),
         ("Good to know", (("Authors are the folders named Last, First. Opened books and bookmarks come from "
                            "the X4's own records, so for a card that hasn't been in an X4 that part is left "
                            "out."),)))),
}

def backups_note() -> str:
    """The backups folder in use, said for help: the default, or picked, and whether it's there."""
    if RUN.backups == DEFAULT_BACKUPS:
        return "backups; the default, beside the script"
    problem = backups_problem()
    return f"backups; the folder you picked, but {problem}" if problem else "backups; the folder you picked"


def logs_note(state: dict) -> str:
    """The logs, said for help: what they hold, their limit, and whether they're on."""
    if not state.get("debug_log", True):
        return "a log of each run, when Debug logging is on in Settings; it's off"
    return (f"a log of each run: what it showed, asked and ran, for working out what went wrong. "
            f"{human(LOGS_SPACE)} at most in all, the oldest deleted first; Settings turns it off")


def help_topics(state: dict) -> tuple[HelpPage, ...]:
    """The topics after the tasks. Built when shown, so they name the backups folder in use and whether logging
    is on."""
    return (
        HelpPage(
            "Keys", "moving around the questions",
            "The same keys work in every question.",
            (("Keys", (("↑ ↓  Enter", "move, pick"),
                       ("type", "filter a long list; what you've typed shows under the question"),
                       ("Backspace", "edit the filter"),
                       ("Esc", ("go back: Back in a list, up a level in the card's folders, No on a yes/no question, "
                                "Quit at the menu")),
                       ("Space, a", "tick one, or all, in a tick list"),
                       ("Tab", "complete a typed path"),
                       ("under the line", ("actions, not things listed: ✓ uses the folder you're in, ↑ goes up a "
                                           "level, ← goes back")),
                       ("Ctrl-C", "stop; during a write it waits until that book is done"),
                       ("yellow", "a card left mounted: ejects it"))),)),
        HelpPage(
            "Backups and safety", "what's saved, and what's checked before writing",
            "Before anything on the card changes, the books it replaces or removes and the X4's own records are saved. "
            "Restore puts them back.",
            (("Saved in", ((f"{tilde(RUN.backups)}/<date>/<card>/", "the books, as they were"),
                           (".device-<time>/", "the X4's recent list, bookmarks and progress"),
                           ('Back up packs the whole card into an archive in the same folder; its question, "Save '
                            'the backup where?", is where to pick another.'))),
             ("Before writing", ("The card is confirmed, then checked again before every write.",
                                 "The last question before a change, Go ahead?, names the change.",
                                 "Afterwards, a box lists each book the change added, moved, renamed or removed.",
                                 "Each prepared book is checked; one with a new problem is left as it was.",
                                 "Books are written under a temporary name, then swapped in.",
                                 "Hidden and system folders are never listed or changed.")))),
        HelpPage(
            "Files and settings", "what it remembers, and where",
            "It remembers the last folder and card it used, when each card last changed and was backed up, and "
            "where backups go.",
            (("Files", ((tilde(STATE_FILE), ("the last folder and card, each card's last change and backup, and a "
                                             "backups folder you picked; delete it to forget them")),
                        (tilde(logs_folder()), logs_note(state)),
                        (tilde(RUN.backups), backups_note()),
                        'Pick another backups folder at Back up\'s "Save the backup where?".')),
             ("Settings", ("Debug logging: the menu's Settings turns the log of each run on or off.",
                           ("Keep scrollback: on, everything stays in the terminal, and a line with the time marks "
                            "each return to the menu after a task. Off, each pick from the menu clears the window and "
                            "its scrollback."),
                           ("Screen size, JPEG quality and grayscale sit at the top of xteink-manager.py. They match "
                            "the firmware's X4 profile."))))),
    )


def help_header(overview: bool = True) -> None:
    page_break()
    head = Text.assemble(("┌", "rail"), "  ", ("XTEINK Manager", "bold"), (" · Help", "accent"))
    version = Text(f"v{VERSION}", style="version")
    console.print(head + Text(" " * max(2, min(console.width, 80) - head.cell_len - version.cell_len)) + version)
    if overview:
        say(TAGLINE)
        say()
        say(ABOUT)
    say()


def column_lines(rows, room: int, widest: int = 32) -> list[str]:
    """Help rows as markup lines `room` wide: (left, right) pairs in two columns, the right wrapping within
    its column; a left too long for the column with its right under it; and text, as a bullet. The column fits
    the lefts no longer than `widest`."""
    width = max((len(row[0]) for row in rows if isinstance(row, tuple) and len(row[0]) <= widest), default=0)
    lines = []
    for row in rows:
        if isinstance(row, str):
            lines += [f"{'[heading]•[/]' if i == 0 else ' '} {esc(part)}" for i, part in enumerate(textwrap.wrap(row, room - 2))]
            continue
        left, right = row
        parts = textwrap.wrap(right, max(20, room - width - 2))
        if len(left) > width:
            lines.append(f"[term]{esc(left)}[/]")
            first = " " * width
        else:
            first = left.ljust(width)
        lines += [f"[term]{esc(first if i == 0 else ' ' * width)}[/]  {esc(part)}" for i, part in enumerate(parts)]
    return lines


def show_help_page(page: HelpPage) -> None:
    say(f"[accent][bold]Help › {esc(page.title)}[/][/]")
    say()
    say(esc(page.about))
    for label, rows in page.sections:
        say()
        say(f"[heading]{esc(label)}[/]")
        for line in column_lines(rows, min(console.width, 80) - 5):
            say(f"  {line}")
    say()


def help_menu(state: dict) -> None:
    """The menu's Help: the overview, then a page per topic, until Esc or Close help."""
    help_header()
    topics = [(label, hint, HELP_PAGES[key]) for label, key, hint in TASKS] + [(t.title, t.hint, t)
                                                                               for t in help_topics(state)]
    width = max(len(label) for label, _, _ in topics)
    try:
        while True:
            RUN.task = "Help"
            page = ask_select("Which topic?", [*(option(label, page, hint, width=width) for label, hint, page in topics),
                                               divider(), back("Close help")], echo=False,
                            esc_hint="Esc closes help")
            if page is BACK:
                return
            if RUN.clean_pages:  # Keep scrollback off: each topic, and the topics again, on a clean window
                clear_screen()
                help_header(overview=False)
            show_help_page(page)
            RUN.task = f"Help › {page.title}"
            topics_again = object()
            if ask_select("Where to?", [action_choice("Back to topics", topics_again, "←"), option("Close help", BACK)],
                          echo=False, on_escape=topics_again) is BACK:
                return
            if RUN.clean_pages:
                clear_screen()
                help_header()
    finally:
        RUN.task = ""


def settings_menu(state: dict) -> None:
    """Settings, from the menu: whether each run is logged, and whether earlier pages stay in scrollback."""
    RUN.task = "Settings"
    picked = None
    try:
        while True:
            on = state.get("debug_log", True)
            keep = state.get("keep_scrollback", True)
            logs = saved_logs()
            hint = (f"{plural(len(logs), 'log')} kept, {human(sum(log_size(log) for log in logs))}" if on and logs
                    else "a log of each run, for working out what went wrong")
            picked = ask_select("Which setting?", [
                option(f"Debug logging: [{'on' if on else 'off'}]", "debug_log", hint, width=22),
                option(f"Keep scrollback: [{'on' if keep else 'off'}]", "keep_scrollback",
                       "earlier pages stay above, to scroll back to" if keep else "each task starts on a clean screen",
                       width=22),
                divider(),
                back(),
            ], default=picked, echo=False)
            if picked is BACK:
                return
            if picked == "keep_scrollback":
                keep_scrollback(state, not keep)
            else:
                (logging_off if on else logging_on)(state)
    finally:
        RUN.task = ""


def keep_scrollback(state: dict, keep: bool) -> None:
    """On: every page stays in the terminal, below a line with its time. Off: each pick from the menu clears the
    window and its scrollback first. Either way, from now on."""
    LOG.info("Keep scrollback turned %s in Settings", "on" if keep else "off")
    saved = save_state(state, keep_scrollback=keep)
    RUN.clean_pages = not keep
    if not keep:
        clear_screen()
    intro()
    if keep:
        done("Keep scrollback is on: earlier pages stay above, each below a line with its time.")
    else:
        done("Keep scrollback is off: each pick from the menu clears the window, so only that task is there.")
    if not saved:
        warn(f"That couldn't be saved in {esc(tilde(STATE_FILE))}, so it's {'on' if keep else 'off'} for this run "
             "only.")
    say()


def log_size(log: Path) -> int:
    try:
        return log.stat().st_size
    except OSError:
        return 0


def logging_off(state: dict) -> None:
    """This run's log stops now, and the logs kept so far can go too. No question when there are none."""
    LOG.info("Debug logging turned off in Settings")
    stop_log()
    saved = save_state(state, debug_log=False)
    logs = saved_logs()
    size = sum(log_size(log) for log in logs)
    if logs and ask_confirm(f"Delete the {plural(len(logs), 'log')} kept so far ({human(size)})?", True):
        for log in logs:
            with suppress(OSError):
                log.unlink()
        done(f"Debug logging is off, and {plural(len(logs), 'log')} deleted.")
    else:
        done("Debug logging is off." + (" The logs kept so far stay." if logs else ""))
    if not saved:
        warn(f"That couldn't be saved in {esc(tilde(STATE_FILE))}, so it's off for this run only.")
    say()


def logging_on(state: dict) -> None:
    """This run is logged from here on, and every run after."""
    saved = save_state(state, debug_log=True)
    start_log(RUN.argv)
    if RUN.log:
        done(f"Debug logging is on. This run is logged from now on, in {esc(tilde(RUN.log))}.")
    else:
        warn(f"Debug logging is on, but {esc(tilde(logs_folder()))} can't be written.")
    if not saved:
        warn(f"That couldn't be saved in {esc(tilde(STATE_FILE))}, so it's on for this run only.")
    say()


def print_help() -> None:
    """--help: the overview and every flag on one screen. The menu's Help has a page for each task."""
    console.print(f"[bold]XTEINK Manager[/] [version]v{VERSION}[/]")
    console.print(TAGLINE)
    console.print()
    console.print(ABOUT)
    console.print()
    console.print("[heading]Tasks[/]")
    flags, labels = max(len(key) for _, key, _ in TASKS) + 4, max(len(label) for label, _, _ in TASKS) + 2
    for label, key, hint in TASKS:
        console.print(f"  [term]{'--' + key:<{flags}}[/][bold]{label:<{labels}}[/]{hint}")
    console.print(f"  {'':<{flags + labels}}[term]--clean[/] or [term]--optimize[/]: one half of Prepare")
    console.print()
    console.print("[heading]Options[/]")
    for line in column_lines((("PATH", "a book, folder or card, so it isn't asked for (Restore: where to)"), DRY_RUN, YES,
                              ("--no-backup", "don't save originals first"),
                              *PREPARE_OPTIONS, ("-h, --help", "this screen"), ("-V, --version", "the version")),
                             min(console.width, 80) - 2, widest=16):
        console.print(f"  {line}")
    console.print()
    console.print("Run it with no options for the menu. Its Help has a page for each task.")
    console.print(f"[hint]More in {esc(tilde(Path(__file__).resolve().parent / 'MANUAL.md'))}[/]")


TASK_FLAGS = ("add", "move", "remove", "prepare", "clean", "optimize", "backup-card", "restore", "check", "stats")
FLAG_STEPS = {"prepare": Steps(True, True), "clean": Steps(True, False), "optimize": Steps(False, True)}


TASK_TITLES = {key: label for label, key, _ in TASKS} | {"clean": "Clean books", "optimize": "Optimize books"}


def run_task(task: str, opts: Options, state: dict, *, from_menu: bool = False):
    RUN.task, RUN.day, RUN.task_failed = TASK_TITLES[task], today(), False
    try:
        if task in FLAG_STEPS:
            return task_prepare(opts, state, None if from_menu else FLAG_STEPS[task])
        return {"add": task_add, "move": task_move, "remove": task_remove, "restore": task_restore,
                "backup-card": task_backup, "check": task_check, "stats": task_stats}[task](opts, state)
    finally:
        RUN.task = ""


def menu_tasks() -> list:
    """The tasks, each under its group's heading."""
    found = {task: (label, hint) for label, task, hint in TASKS}
    choices = []
    for heading, tasks in MENU_GROUPS:
        choices.append(group(heading))
        choices += [option(found[task][0], task, found[task][1], width=16) for task in tasks]
    return choices


def clean_page(picked) -> None:
    """Keep scrollback off: each pick from the menu clears the window and its scrollback, so a task's result
    stays in view until the next pick. Quit doesn't, so the last result stays once the script ends."""
    if not RUN.clean_pages or picked is QUIT:
        return
    clear_screen()
    if picked != "help":  # Help's own header names it
        intro()


def menu(opts: Options, state: dict) -> None:
    """The menu, until Quit: a task that finishes, or is backed out of, comes back to it. Above it, any card
    plugged in that changed since its last whole-card backup is named. A card a task left mounted gets an item
    of its own, in yellow, to eject it; Quit offers that too."""
    RUN.in_menu = True
    while True:
        for reminder in backup_reminders(state):
            warn(reminder)
        picked = ask_select("What do you want to do?", [
            *menu_tasks(),
            group(),
            *(action_choice(f"Eject {card.name}", card, "⏏", style="warn", hint="still mounted")
              for card in cards_left_mounted()),
            option("Help", "help", "what each task does", width=16),
            option("Settings", "settings", "logging, scrollback", width=16),
            option("Quit", QUIT, width=16),
        ], on_escape=QUIT, esc_hint="", on_pick=clean_page)
        if picked is QUIT:
            if not before_quitting(state):
                outro("Bye.")
            return
        if picked == "help":
            help_menu(state)
            say()
            continue
        if picked == "settings":
            settings_menu(state)
            continue
        if isinstance(picked, Card):
            RUN.task, RUN.task_failed = "Eject", False
            try:
                eject_now(picked)
            finally:
                RUN.task = ""
            console.print()
            intro()
            continue
        if run_task(picked, opts, state, from_menu=True) is BACK:
            say()
        else:  # the task closed its block with └; the menu opens the next one
            console.print()
            intro()


def parse_args(argv: list[str]) -> Options:
    """One task flag at most, the options, and an optional path. -h or --help anywhere shows
    help, whatever else is there, short flags run together (-nh) included."""
    if any(word == "--help" or re.fullmatch(r"-[A-Za-z]*h[A-Za-z]*", word) for word in argv):
        return Options(task="help")
    parser = build_parser()
    args, extra = parser.parse_known_args(argv)
    if extra:
        raise argparse.ArgumentError(None, unknown_words(extra, parser))
    if not 1 <= args.quality <= 100:
        raise argparse.ArgumentError(None, "--quality takes a number from 1 to 100.")
    if args.path and args.task in (None, "help", "version"):
        raise argparse.ArgumentError(None, "Say what to do with that path: "
                                           + ", ".join(f"--{task}" for task in TASK_FLAGS) + ".")
    return Options(**vars(args))


def unknown_words(extra: list[str], parser: argparse.ArgumentParser) -> str:
    """What to say about words the parser didn't take: a mistyped option, with the likely one, or a second path."""
    options = [flag for action in parser._actions for flag in action.option_strings]  # argparse has no public list
    for word in extra:
        if word.startswith("-"):
            close = difflib.get_close_matches(word.split("=")[0], options, n=1)
            return f"There's no {word} option." + (f" Did you mean {close[0]}?" if close else "")
    return "Give one book or folder. For several books, give the folder they're in."


def build_parser() -> argparse.ArgumentParser:
    # no abbreviations: --n would be taken for --no-backup, and a new option could change what a short one means
    parser = argparse.ArgumentParser(prog="xteink-manager", add_help=False, exit_on_error=False, allow_abbrev=False)
    one_of = parser.add_mutually_exclusive_group()
    for name in TASK_FLAGS:
        one_of.add_argument(f"--{name}", dest="task", action="store_const", const=name)
    one_of.add_argument("-h", "--help", dest="task", action="store_const", const="help")
    one_of.add_argument("-V", "--version", dest="task", action="store_const", const="version")
    parser.add_argument("path", nargs="?")
    parser.add_argument("-n", "--dry-run", action="store_true")
    parser.add_argument("--no-backup", dest="backup", action="store_false")
    parser.add_argument("-y", "--yes", action="store_true")
    parser.add_argument("-f", "--force", action="store_true")
    parser.add_argument("-q", "--quality", type=int, default=JPEG_QUALITY)
    parser.add_argument("--keep-fonts", action="store_true")
    parser.add_argument("--keep-comments", action="store_true")
    return parser


def main(argv: list[str] | None = None) -> int:
    RUN.reset()
    for stream in (sys.stdout, sys.stderr):  # a name Linux couldn't read as UTF-8 prints escaped, not as a crash
        with suppress(AttributeError, ValueError):
            stream.reconfigure(errors="backslashreplace")
    try:
        opts = parse_args(sys.argv[1:] if argv is None else argv)
    except argparse.ArgumentError as error:
        errors.print(f"[bad]{esc(str(error))}[/]")
        errors.print(f"[hint]{PROG} --help lists the options.[/]")
        return 2
    if opts.task == "help":
        print_help()
        return 0
    if opts.task == "version":
        print(f"xteink-manager {VERSION}")
        return 0
    if not (IS_MAC or sys.platform.startswith("linux")):
        errors.print("[bad]xteink-manager runs on macOS and Linux.[/]")
        return 2
    RUN.interactive = all(stream is not None and stream.isatty() for stream in (sys.stdin, sys.stdout))
    headless_ok = opts.path and (opts.task in ("check", "stats") or (opts.task in FLAG_STEPS and (opts.yes or opts.dry_run)))
    if not RUN.interactive and not headless_ok:
        print_help()
        errors.print("[warn]xteink-manager asks questions as it goes, so run it in a terminal. Without one, only "
                     "--check or --stats with a path, or --prepare, --clean or --optimize with a path and --yes or "
                     "--dry-run, work.[/]")
        return 2

    RUN.argv = sys.argv[1:] if argv is None else argv
    state = load_state()
    if state.get("debug_log", True):
        start_log(RUN.argv)
    else:
        stop_log()
    for sig in (signal.SIGTERM, signal.SIGHUP):  # stop as Ctrl-C does, so the cleanup on the way out runs
        signal.signal(sig, stop_on_signal)
    try:
        RUN.backups = backups_from(state)
        if opts.task:  # a task from the command line is one page, so it always stays in scrollback
            intro()
            if run_task(opts.task, opts, state) is BACK:
                outro("Nothing changed.")
            if RUN.interactive and cards_waiting():  # the task's block is closed: the question gets one of its own
                console.print()
                page_break()
                console.print(Text.assemble(("┌", "rail"), "  ", ("Before quitting", "bold")))
                say()
                before_quitting(state)
        else:
            RUN.clean_pages = not state.get("keep_scrollback", True)
            intro()
            menu(opts, state)
        return 1 if RUN.failed else 0
    except (KeyboardInterrupt, EOFError) as stop:  # EOFError: Ctrl-D in an empty field
        errors.print()
        signum = getattr(stop, "signum", signal.SIGINT)
        return stopped("Cancelled." if signum == signal.SIGINT else f"Stopped by {signal.Signals(signum).name}.",
                       128 + signum)
    except NeedsTerminal as question:
        fail(f"That needs an answer ({esc(str(question))}), and there's no terminal to ask in.")
        return stopped("Stopped.", 2)
    except SafetyError as error:
        fail(esc(str(error)))
        return stopped("Stopped to be safe.", 1)
    except OSError as error:
        fail(esc(f"{error.strerror or error}: {error.filename or ''}".rstrip(": ")))
        return stopped("Stopped.", 1)
    except Exception:  # the last resort: any bug is shown and logged, then the run stops as any other does
        traceback.print_exc()
        LOG.exception("a bug")
        fail("That's a bug in xteink-manager; the details are above.")
        return stopped("Stopped.", 1)


if __name__ == "__main__":
    sys.exit(main())
