# xteink-manager manual

[Synopsis](#synopsis) · [Requirements](#requirements) · [Linux](#linux) · [Options](#options) · [Getting around](#getting-around) · [Tasks](#tasks) · [Settings](#settings) · [Files](#files) · [Safety](#safety) · [Exit status](#exit-status) · [Uninstall](#uninstall)


## Synopsis

```
xteink-manager
xteink-manager --add | --move | --remove | --prepare | --clean | --optimize
               | --backup-card | --restore | --check | --stats  [PATH] [options]
xteink-manager --help | --version
```

With no options, the script opens a menu and asks questions as it goes. A task option skips the menu and runs just that task. A path after it (a book, a folder or the card) skips the question that would ask for it. For Restore, the path is where the books go back to.

The card is the X4's library. Books sit in genre folders, filed by author, like `[ Classics ]/Austen, Jane/Emma.epub`. CrossPoint keeps each book's reading progress, bookmarks and cache under the book's path on the card. When a book is moved or renamed in Finder, the X4 loses its place in that book. The script moves those records along with the book.


## Requirements

- macOS or Linux, and [uv](https://docs.astral.sh/uv/). On the first run, uv fetches Python 3.14 or newer and the four packages the script needs.
- An XTEINK X4 running [CrossPoint](https://github.com/crosspoint-reader/crosspoint-reader), the open-source replacement firmware. The script follows CrossPoint 1.6.5: where it keeps reading progress, and what its "Optimize EPUB" does.
- [par2](https://github.com/Parchive/par2cmdline) adds repair data to backups. It's optional. Without it, backups still get a checksum for every file.


## Linux

The same script runs on Linux. It finds cards with `lsblk` and ejects them with udisks2. Without udisks2, the script can't eject a card, so it never offers to; unmount the card yourself before you pull it out. The script's tests run on macOS only, so Linux use is untested.


## Options

A task option runs one task. Use one at a time. Options can't be shortened, so `--check` works but `--ch` doesn't.

| Option | Runs |
|---|---|
| `--add` | [Add books](#add-books) |
| `--move` | [Move or rename](#move-or-rename) |
| `--remove` | [Remove books](#remove-books) |
| `--prepare` | [Prepare books](#prepare-books): clean, then optimize |
| `--clean`, `--optimize` | One half of Prepare |
| `--backup-card` | [Back up](#back-up) |
| `--restore` | [Restore](#restore) |
| `--check` | [Check books](#check-books) |
| `--stats` | [Stats](#stats) |

The rest change how a task runs:

| Option | Does |
|---|---|
| `-n`, `--dry-run` | Shows what would change, and changes nothing |
| `--no-backup` | Doesn't save the books a task replaces or removes. The X4's reading records are saved anyway |
| `-y`, `--yes` | Skips "Go ahead?" in Add and Prepare. Other questions are still asked |
| `-f`, `--force` | Optimizes again books that were already optimized |
| `-q N`, `--quality N` | JPEG quality for optimized images, 1 to 100. The default is 85, the same as CrossPoint's |
| `--keep-fonts`, `--keep-comments` | Optimizes without removing embedded fonts, or comments |
| `-h`, `--help` | Lists the tasks and options. If it's anywhere on the line, help is all that runs |
| `-V`, `--version` | Prints the version |

A mistyped option gets a suggestion, like "Did you mean --check?".

**Without a terminal**, such as from cron or another script, the script can't ask questions, so only these run:

- `--check` or `--stats` with a path, like `xteink-manager --check "/Volumes/XTEINK X4"`.
- `--prepare`, `--clean` or `--optimize` with a path and `--yes` or `--dry-run`.

Anything else prints the help and exits with status 2.


## Getting around

| Key | Does |
|---|---|
| ↑ ↓ and Enter | Move and pick |
| Type | Filter a long list. What you've typed shows under the question |
| Backspace | Edit the filter |
| Space, a | Tick one item, or all of them, in a tick list |
| Tab | Complete a typed path |
| Esc | Go back: **Back** in a list, up one level in the card's folders, No on a yes/no question, Quit at the menu. In a filtered list it clears the filter first |
| Ctrl-C | Stop. While a book and its reading records are changing, the script waits until that book is done |

- Lists show the items first, like books, folders or cards. Below a line are the actions, in their own color: ✓ uses the folder you're in, ↑ goes up a level, → looks elsewhere, ← goes back.
- The line above each question says what's being done to what, like "Moving  [ History ]/Gibbon, Edward/". Once you've confirmed the card, its name, book count and free space sit at the right of that line.
- Before a change, "Go ahead?" asks. The first answer spells out the change, like **Copy 3 books**, and the last is **Back**. When the change removes books or replaces them from a backup, the last answer is **No** and the highlight starts on it, so pressing Enter right away cancels.
- After a change, a box titled with the card's name lists each book added (+), replaced (↻), moved (→), renamed (✎) or removed (−), and how many books the card holds now.
- After a task, the menu comes back. Later tasks reuse the confirmed card until it's ejected, or a drive is plugged in or removed.
- Each time the menu comes back after a task, and each time Help opens, a line with the time marks the spot, so the newest is easy to find when you scroll back. To start each task on a clean screen instead, turn off [Keep scrollback](#keep-scrollback).

### The menu

| Group | Tasks |
|---|---|
| On the card | Add books, Move or rename, Remove books, Prepare books |
| Backups | Back up, Restore |
| Info | Check books, Stats |

Below those are Help, with a page for each task, then Settings and Quit. If the script has changed a plugged-in card since its last whole-card backup, a reminder shows above the menu. Changes made in Finder don't count, since the script can't know about them.

### Picking the card

You pick the card from the removable drives. The computer's own drives never show up. The script shows the card's size, how many books it holds and its genre folders, then asks "Is this the right card?".

Some cards are greyed out for the tasks that change the card: a card that isn't FAT or exFAT, a locked card, a card with no volume ID (the script checks that ID before every write), and a card mounted inside a system folder. Back up, Check books and Stats only read the card, so they can still use a locked card or one with no volume ID.

A card without a `.crosspoint` folder gets a warning: it hasn't been in an X4 running CrossPoint yet, or it isn't the X4's card.

### Keeping the card mounted

A task that used the card ends by asking **Eject** or **Keep it mounted**, for another task. From the command line the second answer is **Leave it mounted**. Esc keeps it.

While a card is still mounted, the menu shows a yellow **Eject** item for it. When you quit, the script names each card you used that's still mounted and offers to eject it. Without a terminal, nothing is asked and the card stays mounted. On Linux without udisks2, the script never offers to eject; see [Linux](#linux).


## Tasks

### Add books

`--add` · Copies books from this computer onto the card, prepared for the X4 on the way.

- "Books to add?" takes a folder of books or one `.epub` file.
- "Prepare them first?" offers to optimize the books, and to clean any that look like archive.org scans. See [Prepare books](#prepare-books). **Copy as they are** skips both.
- Each book is named from its own title and author, like `Austen, Jane/Emma.epub`. A leading "The" or "A" moves to the end, as in `Prince, The.epub`. Garbled characters in names, like `H｣rin`, are repaired.
- "Genre folder for these books?" lists the card's genre folders. **Pick for each book** asks per book, and **New genre folder…** makes one.
- Before copying, the script lists where each book goes. It flags a book that would replace a different book with the same name, and a new genre folder. **Change a name or folder** at "Go ahead?" lets you fix one.
- A book that's exactly the same as the copy on the card is skipped. A book that replaces an older copy of itself keeps its reading progress and bookmarks when its chapters are the same; otherwise it opens at the start.

### Move or rename

`--move` · Renames a book or a folder where it is, or moves it to another folder. Its reading progress, bookmarks and place in the recent list go with it.

- Pick the book or folder, then **Rename it** or **Move it**. A move keeps the name; pick the folder it goes into, or type one.
- A name the card can't store is refused as you type, and so is a name already taken there.
- After each change, the script asks if you want to move or rename something else.

### Remove books

`--remove` · Takes books off the card, along with their reading progress, bookmarks and cache.

- Pick one book, or a folder and then which books in it.
- A copy of each book is saved to the backups folder first, so Restore can put it back. `--no-backup` skips the copy.
- "Go ahead?" starts on **No**.
- Folders left empty are removed, except the genre folders at the top of the card.

### Prepare books

`--prepare` · Cleans and optimizes books already on the card: all of it, a folder or one book. It also works on a folder on this computer. `--clean` and `--optimize` run one step each.

- **Optimize** does what CrossPoint's own "Optimize EPUB" does. It turns images into grayscale JPEGs that fit the 480 × 800 screen, removes embedded fonts and comments, and adds a little CSS that keeps tables and code inside the page. A book that's already optimized is skipped, unless you use `--force`.
- **Clean** repairs the books archive.org makes from page scans: run-on paragraphs, running headers and page numbers, junk pages, duplicate scans and a missing table of contents. It also merges books made of one file per page into chapters, so the X4 doesn't stall turning pages.
- Clean runs only on books that look like those scans: made with ebooklib, with page-scan images, and with archive.org's notice page or nearly every page a single run-on paragraph. Clean would damage a well-made book, so it never runs on one.
- Every prepared book is checked before it replaces the original. See [Safety](#safety).
- A book locked with DRM by the store that sold it is left as it was. The X4 can't open it either way.

### Back up

`--backup-card` · Packs every book on the card into one archive: the EPUBs, the other files the X4 opens, and the X4's reading progress, bookmarks and recent list. It saves a checksum for every file, reads the archive back from the drive to check each one, then adds repair data.

The other files are TXT, MD and XTC files, plus the pictures the X4 shows while it sleeps: `sleep.bmp` and the pictures in the `sleep` folder, and their overlay versions. Counts call them "other files".

"Into?" offers a new dated backup, or a kept-current one.

A dated backup gets its own folder and is never changed. Its files are named after the card:

```
xteink-backups/2026-11-02/XTEINK X4 (whole card)/
  XTEINK X4.tar.zst           the archive: a standard tar, compressed with zstd
  XTEINK X4.tar.zst.sha256    a checksum for every file; shasum -a 256 -c reads it too
  XTEINK X4.tar.zst.par2      repair data, plus .vol files, when par2 is installed
```

A kept-current backup is the one you update after each change, instead of piling up dated ones. Pick **Start a kept-current backup** the first time. After that, **Update** comes first.

```
xteink-backups/XTEINK X4 (kept current)/
  XTEINK X4.tar.zst           the same three files as a dated backup
  XTEINK X4.tar.zst.sha256
  XTEINK X4.tar.zst.par2
```

- A compressed archive can't be patched, so each update re-reads the whole card. It needs room for two copies until the new one checks out.
- Before updating, the script lists what changes. When books would be dropped from the backup, "Go ahead?" starts on **Back**. A book that's only in another folder now counts as moved, not dropped.
- A book that changed since the last update and won't open now is shown, and you're asked before the new copy replaces the backup's.
- The new copy is built in a hidden folder beside the old one and moves in only once it reads back cleanly. A stopped or failed update leaves the old copy whole. An update stopped while the new copy moves in is finished the next time the script reads that backup.
- A new backup that's stopped before it has read back, or doesn't read back cleanly, is deleted. The card is still there to back up again. One stopped while its repair data is built is kept, without repair data.

The archive is a standard tar, so `tar -xf` unpacks it without the script. The X4's fonts and caches aren't in it, since the X4 rebuilds its caches itself.

"Save the backup where?" starts at the backups folder in use. Once the backup goes ahead, a folder you pick there is used for every backup from then on. A FAT drive is refused when the backup would pass 4 GB, the largest file FAT can hold.

### Restore

`--restore` · Puts books back on the card, or into a folder on this computer: from a whole-card backup, or from the copies saved before books changed or were removed.

- "Restore from?" lists the backups of that card in the backups folder in use. **Look in another folder…** finds older ones.
- "Which books?" is a tick list. It includes the backup's other files, such as `sleep.bmp`.
- A book from an archive is checked against its checksum before anything is written. A book that's damaged in the backup is left out.
- A damaged archive with repair data is repaired first, which needs par2. A repair that's stopped or fails leaves the archive as it was.
- A book that replaces one on the card keeps its reading progress when its chapters are the same. The book it replaces is saved first.
- "Go ahead?" starts on **No**.

### Check books

`--check` · Finds books that won't open, or checks a backup. It changes nothing. "Check what?" offers three things:

- **All of** the card, or **One book, or a folder…**: the script reads every book and lists the ones that won't open or are missing parts, and says when Restore has a saved copy. Harmless quirks, like a publisher's image the book never included, are only counted.
- **A backup of it…**: the script checks the backup's repair data, then reads every file in the archive and compares it with its checksum. A backup without its checksum list fails the check, since Restore can't use it; `tar -xf` still unpacks it. `--check` followed by a `.tar.zst` file checks that backup.

### Stats

`--stats` · Shows the library at a glance: books, authors and genres, with a bar for each genre, how full the card is, which books have been opened on the X4 and bookmarked, the recently read list, and the last backup. No book is opened, so it's quick.

A genre is a folder at the top of the card that holds books. An author is a `Last, First` folder inside a genre.


## Settings

The menu's Settings has two settings, both on by default.

### Debug logging

Each run writes a log of what it showed, what it asked, what you answered, every command it ran, and every change to the card. When a run stops or crashes, its last lines name the log.

- Each run writes its own log file. When the script starts, it deletes the oldest log files, a whole run at a time, so that all the logs together stay under 5 MB.
- If one run's log grows past 1 MB, it stops noting each file one by one. It still notes what the script showed, what you answered, and what changed. Past 2 MB, that run's log stops.
- Turning logging off stops the current log right away and offers to delete the old ones.

### Keep scrollback

With Keep scrollback on, the default, everything the script shows stays in the terminal, so you can scroll back through the whole session. Each time the menu comes back after a task, and each time Help opens, a line with the time marks the spot. The time matches the log's.

With Keep scrollback off, each pick from the menu clears the terminal window and its scrollback, so only the task you picked is there. Quit doesn't clear, so the last result stays after the script ends.

- The first clear also removes whatever was in the terminal window before you started the script.
- A task run from the command line, like `--add`, always keeps its output.


## Files

| Where | What |
|---|---|
| `~/.config/xteink-manager/state.json` | What the script remembers: the last folder and card, when each card last changed and was backed up, your backups folder, and your [Settings](#settings). Delete it to forget them, and both settings go back on. Uses `$XDG_CONFIG_HOME` instead of `~/.config` when that's set |
| `~/.config/xteink-manager/logs/` | A log of each run, beside `state.json`. See [Debug logging](#debug-logging) |
| `xteink-backups/` | Where backups go: next to the script, unless you pick another folder |

Before any change, the script saves what the change replaces or removes into the backups folder:

```
xteink-backups/2026-11-02/XTEINK X4/
  [ Classics ]/Austen, Jane/Emma.epub    the book, as it was before it changed
  .device-<time>/                        the X4's recent list, open book, bookmarks and progress
```

A different book that later had the same path, or another card with the same name, gets its own folder, `XTEINK X4 (2)`, so nothing is overwritten.

A few rarely changed settings sit at the top of `xteink-manager.py`: the screen size, JPEG quality and grayscale (which match CrossPoint's X4 profile), the default backups folder, how much room the logs may take, the compression level, and how much repair data backups get.


## Safety

- Before a task changes the card, the script shows what's on it and asks if it's the right one. It skips that question when you named the card on the command line, or confirmed it earlier in the run.
- Before every write, the script checks the card's ID to make sure the same card is still there. A swapped card stops the run.
- Every task shows the full list of changes before anything is written.
- In a filtered list, Enter does nothing until the filter matches, so a typo can't pick the first item.
- A prepared book replaces the original only if it's a readable EPUB with no problem the original didn't already have: missing files, broken images or links, or a broken reading order. Every page that was valid XML must still be, and optimizing must leave every page's words exactly as they were.
- Books are written under a temporary name beside the original, flushed to the card, and only then swapped in, so a cut-short write never leaves half a book. A temporary copy with no finished book beside it may be the only copy, so the script reports it and never deletes it.
- If you press Ctrl-C, or the run gets a `kill`, while a book and its reading records are changing, the script waits until that book is done.
- System folders never show up and can't be typed or given on the command line: hidden folders like `.crosspoint`, the X4's `fonts` folder, and Windows' `System Volume Information`.
- After a change, the script sweeps macOS's `._` and `.DS_Store` files off the card.
- The folder you add books from is only ever read.


## Exit status

| Code | Means |
|---|---|
| 0 | Everything went well, or you said no |
| 1 | Something failed, or Check books found a damaged book or backup |
| 2 | An option it doesn't know, two tasks at once, a path with no task, no terminal, or a system other than macOS or Linux |
| 130 | Stopped with Ctrl-C, or Ctrl-D in an empty field |
| 128 + N | Stopped by signal N, like a `kill` or a closed terminal |

Warnings and errors go to stderr.


## Uninstall

```bash
rm ~/.local/bin/xteink-manager                            # the launcher, if you made one
rm -r "${XDG_CONFIG_HOME:-$HOME/.config}/xteink-manager"  # what it remembers, and the logs
uv cache prune                                            # the script's cached environment
```

uv still keeps the packages it downloaded. `uv cache clean` empties its cache, and `uv python uninstall <version>` removes the Python it fetched, if it fetched one. `uv python list --only-installed` shows which version that is. Do either only if nothing else of yours uses uv.

Then delete the folder. Move `xteink-backups/` somewhere safe first: your backups are in it.
