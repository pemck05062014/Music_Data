#!/usr/bin/env python3
#V4: skip completed row or with "missing info" in 'last_updated'
"""
getsongbpm_music_logger.py
 
A smaller, standalone version of the music-logging script that ONLY talks
to GetSongBPM.com -- no Spotify calls at all. Useful if you just want the
tempo/key/time-signature/danceability/acousticness numbers without
setting up Spotify developer credentials.
 
WHAT THIS SCRIPT DOES
----------------------
Walks every ".m4a" file under the Music Directory you give it, and for
each one:
  - Reads the artist / album / track title straight out of the folder and
    file names (no API call needed for these -- see the folder layout
    below).
  - Looks the track up on GetSongBPM.com's free API to get tempo, key,
    time signature, danceability, and acousticness.
  - Writes one row per track to a CSV file.
 
Folder / file names are expected to look like this:
    <root path>/.../<directory>/<artist>/<album>/<## track title>.m4a
i.e. the two folders directly above the file are the ALBUM and the ARTIST,
and the file name itself starts with a track number, e.g. "03 Yellow.m4a".
 
RUNNING IT
----------
    python getsongbpm_music_logger.py "/path/to/Music Directory"
 
You need a free API key from https://getsongbpm.com/api, set as an
environment variable before you run the script:
 
    export GETSONGBPM_API_KEY="xxxxxxxx"
 
PYTHON PACKAGES YOU NEED (run once, before using the script):
    pip install requests --break-system-packages
 
RE-RUNNING THE SCRIPT
----------------------
Each time you run this, it checks the CSV for every track: if that track
already has a row at all -- whether last_updated has a real date in it,
or says "missing info" because GetSongBPM had nothing for it last time
-- it's skipped, no API call spent on it. Only tracks with no row yet
get looked up. This way a re-run never spends API calls on a track it
has already tried, on purpose: GetSongBPM not knowing a track once
usually means it still won't next time, so retrying it burns calls
without much chance of a different result. If you ever want a "missing
info" track retried, just delete its row from the CSV (or clear its
last_updated cell) and re-run.
 
------------------------------------------------------------------------
WHAT'S IN THE CSV (and what got left out on purpose)
------------------------------------------------------------------------
This CSV only has the columns GetSongBPM can actually fill in, plus the
path/date columns and the artist/album/track names read from your folder
structure:
 
    path, last_updated, artist, album, track,
    track_tempo, track_key, track_timeSignature,
    track_danceability, track_acousticness
 
track_key is derived from exactly what GetSongBPM returns in their
"key_of" field (e.g. "Em", "C", "F#m"), but is expanded before being
saved. GetSongBPM still encodes the mode in that same string (a
trailing "m" means minor, no "m" means major), so there's no separate
track_mode column here -- but the saved value now:
  - Shows both the sharp and flat spelling for any accidental note,
    e.g. "A#" is saved as "A♯/B♭" (natural notes like "C" or "G" have
    no alternative spelling, so they're left as-is).
  - Is followed by the key's dominant, subdominant, and relative
    major/minor key, e.g.:
        "A♯/B♭ [dom: F | sub: D♯/E♭ | rel: Gm]"
  - If GetSongBPM's key string can't be parsed (unexpected format),
    the original string is saved unchanged as a fallback.
 
Everything Spotify-only (artist_genre, artist_popularity, album_genre,
album_popularity, track_popularity) and everything neither Spotify nor
GetSongBPM can honestly provide anymore (track_energy, track_loudness,
track_instrumentalness, track_liveness, track_speechiness, track_valence)
has been dropped from this version entirely, since this script has no way
to fill them in. If you want those too, use the other script
(spotify_music_logger.py), which combines Spotify + GetSongBPM + local
audio analysis to cover the full column set.
 
Note: "artist", "album", and "track" here come from your folder/file
names, not from GetSongBPM's own record of the song -- so they'll exactly
match how your files are organized, even if that differs slightly from
how GetSongBPM spells the artist or track name. This also means these
three columns get filled in for every track, even ones GetSongBPM has no
data for.
"""

import os
import sys
import re
import csv
import time
import argparse
from pathlib import Path
from datetime import datetime

import requests


# ==========================================================================
# STEP 0: CONSTANTS - the CSV column layout, and lookup tables
# ==========================================================================

CSV_COLUMNS = [
    "path",
    "last_updated",
    "artist",
    "album",
    "track",
    "track_tempo",
    "track_key",
    "track_timeSignature",
    "track_danceability",
    "track_acousticness",
]

CSV_FILENAME = "_A_Music-GetSongBPM-Info_A_.csv"

# GetSongBPM's free tier allows up to 3000 requests/hour, so hitting a
# rate limit here is unlikely -- but just in case, retry a couple of
# times with a short wait before giving up on that ONE track (unlike the
# Spotify script, a rate limit here doesn't stop the whole program).
MAX_RETRIES = 1
RETRY_WAIT_SECONDS = 5

# A row only counts as "already done" (and gets skipped on a re-run) if
# its last_updated column is filled in with an actual date -- i.e. it's
# neither blank (no row yet) nor "missing info" (GetSongBPM had nothing
# for this track last time). Individual data columns like track_tempo or
# track_key are NOT required to be non-empty for a row to be skipped:
# GetSongBPM doesn't always return every field even for a successful
# match, so requiring them too would mean some tracks get needlessly
# re-looked-up forever. Feel free to add columns to this list if you'd
# rather be stricter about what counts as "complete."
REQUIRED_COLUMNS_FOR_COMPLETE = []

# GetSongBPM's free tier caps out at 3000 requests/hour. Rather than run
# right up to that limit (and risk getting hard rate-limited or blocked),
# the script keeps its own running count of calls made this run and
# stops itself early, once it gets within 50 calls of the ceiling.
MAX_API_CALLS_PER_RUN = 2950
api_call_count = 0  # incremented once per real request sent to GetSongBPM

 
# ==========================================================================
# STEP 1: SMALL HELPER FUNCTIONS
# ==========================================================================

# --------------------------------------------------------------------
# Music-theory lookup tables, used to expand a GetSongBPM "key_of"
# string (e.g. "F#m") into the richer saved format (e.g.
# "F♯/G♭m [dom: C♯/D♭m | sub: Bm | rel: A"). Index 0-11 is C, C#/Db,
# D, ... B, going up in semitones (standard pitch-class numbering).
# --------------------------------------------------------------------
SHARP_NAMES = ["C", "C♯", "D", "D♯", "E", "F", "F♯", "G", "G♯", "A", "A♯", "B"]
FLAT_NAMES = ["C", "D♭", "D", "E♭", "E", "F", "G♭", "G", "A♭", "A", "B♭", "B"]
# Natural notes (white keys) have only one spelling, so they don't get
# a "sharp/flat" alternative -- only the 5 black-key notes do.
NATURAL_PITCH_CLASSES = {0, 2, 4, 5, 7, 9, 11}

# Maps a letter name to its pitch class (semitones above C).
LETTER_TO_PITCH_CLASS = {"C": 0, "D": 2, "E": 4, "F": 5, "G": 7, "A": 9, "B": 11}

# Recognizes a GetSongBPM-style key string: a letter A-G, an optional
# sharp/flat accidental (ASCII or unicode), and an optional trailing
# "m" for minor.
KEY_STRING_RE = re.compile(r"^\s*([A-Ga-g])\s*([#♯b♭]?)\s*(m?)\s*$")


def parse_key_string(key_string):
    """
    Parses a GetSongBPM-style key string (e.g. "F#m", "Bb", "C") into
    (pitch_class, is_minor). Returns None if the string doesn't match
    the expected letter[accidental][m] pattern.
    """
    if not key_string:
        return None

    match = KEY_STRING_RE.match(key_string)
    if not match:
        return None

    letter, accidental, minor_flag = match.groups()
    pitch_class = LETTER_TO_PITCH_CLASS[letter.upper()]

    if accidental in ("#", "♯"):
        pitch_class += 1
    elif accidental in ("b", "♭"):
        pitch_class -= 1

    pitch_class %= 12
    return pitch_class, bool(minor_flag)


def format_pitch_class(pitch_class, is_minor):
    """
    Turns a pitch class (0-11) + mode back into a display string, e.g.
    pitch_class=10, is_minor=True -> "A♯/B♭m". Natural notes (no
    accidental) are shown with just their single letter name, e.g.
    pitch_class=7, is_minor=False -> "G".
    """
    if pitch_class in NATURAL_PITCH_CLASSES:
        name = SHARP_NAMES[pitch_class]
    else:
        name = f"{SHARP_NAMES[pitch_class]}/{FLAT_NAMES[pitch_class]}"

    return name + ("m" if is_minor else "")


def build_expanded_key(key_string):
    """
    Expands a GetSongBPM "key_of" string into the richer format we
    save to the CSV: the original key (with sharp/flat alternatives
    shown for accidental notes), followed by its dominant, subdominant,
    and relative major/minor key, e.g.:

        "A#" -> "A♯/B♭ [dom: F | sub: D♯/E♭ | rel: Gm]"

    The dominant and subdominant are a perfect 5th and perfect 4th
    above the tonic, kept in the same mode as the original key. The
    relative key flips the mode (major <-> minor) and shifts by a
    minor 3rd (down for major -> relative minor, up for minor ->
    relative major).

    If key_string can't be parsed, it's returned unchanged so nothing
    is lost -- it just won't have the extra info appended.
    """
    parsed = parse_key_string(key_string)
    if parsed is None:
        return key_string

    pitch_class, is_minor = parsed

    original = format_pitch_class(pitch_class, is_minor)
    dominant = format_pitch_class((pitch_class + 7) % 12, is_minor)
    subdominant = format_pitch_class((pitch_class + 5) % 12, is_minor)

    if is_minor:
        relative = format_pitch_class((pitch_class + 3) % 12, False)
    else:
        relative = format_pitch_class((pitch_class - 3) % 12, True)

    return f"{original} [dom: {dominant} | sub: {subdominant} | rel: {relative}]"


def format_progress_bar(current, total, bar_width=30):
    """
    Builds a simple text progress bar like:
        [######------------------------]  20% (24/120)
    No external dependencies (e.g. tqdm) needed -- just str formatting.
    """
    if total <= 0:
        fraction = 1.0
    else:
        fraction = min(max(current / total, 0.0), 1.0)

    filled = int(round(bar_width * fraction))
    bar = "#" * filled + "-" * (bar_width - filled)
    percent = int(round(fraction * 100))
    return f"[{bar}] {percent:3d}% ({current}/{total})"


def parse_track_path(music_dir, file_path):
    """
    Given the music directory and the full path to a .m4a file, pulls out
    the artist name, album name, and track title from the required folder
    layout: .../<artist>/<album>/<## track title>.m4a
    """
    relative_path = file_path.relative_to(music_dir)
 
    album_name = file_path.parent.name
    artist_name = file_path.parent.parent.name if file_path.parent.parent != music_dir.parent else ""
 
    raw_title = file_path.stem  # filename without the ".m4a"
    # Strip a leading track number like "03 ", "03. ", "03 - " off the title.
    track_title = re.sub(r'^(?:\d{1,2}-\d{2}|\d{1,2})(?:\s*-\s*|\.\s+|\s+)', "", raw_title).strip()
    if not track_title:
        track_title = raw_title  # fallback: no leading number found, use as-is

    return {
        "relative_path": relative_path.as_posix(),
        "artist": artist_name,
        "album": album_name,
        "track_title": track_title,
    }


# ==========================================================================
# STEP 2: CSV SETUP - create the file if it's missing, load whatever rows
#         already exist, and provide a way to check if a row is "done"
#         and a way to safely re-save the whole file as we go.
# ==========================================================================
 
def row_is_complete(row):
    """
    A row counts as complete (safe to skip on a re-run) as soon as it
    exists at all -- that includes rows where last_updated says
    "missing info" (GetSongBPM had nothing for that track last time).
    Those are skipped too, on purpose: re-querying a track GetSongBPM
    already didn't recognize is unlikely to succeed the second time,
    so retrying it would just spend API calls for no real chance of a
    different result. The only tracks that get looked up are ones with
    no row in the CSV yet. Any columns listed in
    REQUIRED_COLUMNS_FOR_COMPLETE (empty by default) must also have a
    value, in case you want to opt back into stricter checking.
    """
    if not row:
        return False

    last_updated = (row.get("last_updated") or "").strip()
    if last_updated in (""):
        return False

    for column in REQUIRED_COLUMNS_FOR_COMPLETE:
        if not (row.get(column) or "").strip():
            return False

    return True
 
 
def load_existing_rows(csv_path):
    """
    Makes sure the CSV file exists with the right header row, then reads
    whatever's already in it into a dict of {path: row}. Using a
    dict (rather than a list) means we can easily look up, update, or add
    a single track's row later without touching the others.
    """
    if not csv_path.exists():
        print(f"'{CSV_FILENAME}' not found -- creating a new one.")
        with open(csv_path, "w", newline="", encoding="utf-8-sig") as f:
            writer = csv.DictWriter(f, fieldnames=CSV_COLUMNS)
            writer.writeheader()
        return {}
 
    print(f"Found existing '{CSV_FILENAME}' -- reading it in.")
    rows_by_path = {}
    with open(csv_path, "r", newline="", encoding="utf-8-sig") as f:
        reader = csv.DictReader(f)
        for row in reader:
            path_value = (row.get("path") or "").strip()
            if path_value:
                # Make sure every expected column exists even if the file
                # on disk is from an older/different version of the script.
                full_row = {column: row.get(column, "") for column in CSV_COLUMNS}
                rows_by_path[path_value] = full_row
 
    complete_count = sum(1 for row in rows_by_path.values() if row_is_complete(row))
    print(
        f"{len(rows_by_path)} row(s) found, {complete_count} already complete "
        "and will be skipped."
    )
    return rows_by_path
 
 
def save_all_rows(csv_path, rows_by_path):
    """
    Rewrites the whole CSV from the rows_by_path dict, in a crash-safe
    way: write everything to a temporary file first, then swap it into
    place, so the real CSV is never left half-written if the script gets
    interrupted mid-save.
    """
    temp_path = csv_path.with_suffix(csv_path.suffix + ".tmp")
    with open(temp_path, "w", newline="", encoding="utf-8-sig") as f:
        writer = csv.DictWriter(f, fieldnames=CSV_COLUMNS)
        writer.writeheader()
        for row in rows_by_path.values():
            writer.writerow(row)
    os.replace(temp_path, csv_path)  # atomic on the same filesystem
 

#==========================================================================
# STEP 3: GETSONGBPM LOOKUP
# ==========================================================================
 
def lookup_getsongbpm(api_key, artist, title):
    """
    Looks a track up on GetSongBPM.com. Returns (found, data) where
    'found' is True/False (was a matching song located at all) and
    'data' is a dict of whatever fields could be parsed out of it.
 
    Retries a couple of times on a rate-limit response (HTTP 429) before
    giving up on just this one track -- it does NOT stop the whole
    program, since GetSongBPM's free-tier limit (3000 requests/hour) is
    generous enough that this should rarely happen.
    """
    for attempt in range(1, MAX_RETRIES + 1):
        global api_call_count
        try:
            response = requests.get(
                "https://api.getsong.co/search/?",
                params={
                    "api_key": api_key,
                    "type": "both",
                    "lookup": f"song:{title} artist:{artist}",
                    "limit": 1,
                },
                timeout=15,
            )
        except requests.RequestException as exc:
            print(f"  [warning] Network error contacting GetSongBPM: {exc}")
            return False, {}

        # Count this as one call made, whether it succeeded or not, then
        # check if we've hit our self-imposed safety limit for the run.
        api_call_count += 1
        if api_call_count >= MAX_API_CALLS_PER_RUN:
            sys.exit(
                f"\nSTOPPING: reached the self-imposed limit of "
                f"{MAX_API_CALLS_PER_RUN} GetSongBPM calls for this run "
                "(staying safely under their 3000/hour free-tier cap). "
                "Your progress so far is already saved in the CSV -- "
                "just re-run the script later (e.g. next hour) and it'll "
                "pick up where it left off; already-complete rows are "
                "skipped automatically."
            )
 
        if response.status_code == 429:
            wait_seconds = int(response.headers.get("Retry-After", RETRY_WAIT_SECONDS))
            print(f"  [rate limited] waiting {wait_seconds}s (attempt {attempt}/{MAX_RETRIES})...")
            time.sleep(1200)
            continue
 
        if response.status_code != 200:
            print(f"  [warning] GetSongBPM returned {response.status_code} for this track.")
            return False, {}
 
        try:
            results = response.json().get("search", [])
        except ValueError:
            return False, {}
 
        # GetSongBPM normally returns a list of matches under "search",
        # but on some errors (bad key, no match, etc.) it returns
        # something else instead (a string or a dict) -- so we only try
        # to read a match out of it if it's actually a non-empty list.
        if not isinstance(results, list) or not results:
            return False, {}
 
        song = results[0]
        if not isinstance(song, dict):
            return False, {}
        data = {}
 
        tempo = song.get("tempo")
        if tempo not in (None, "", "0"):
            try:
                data["tempo"] = round(float(tempo))
            except (TypeError, ValueError):
                pass
 
        time_sig = song.get("time_sig")  # e.g. "4/4"
        if time_sig and "/" in str(time_sig):
            try:
                data["time_signature"] = int(str(time_sig).split("/")[0])
            except ValueError:
                pass
 
        # GetSongBPM gives us e.g. "Em", "C", "F#m" -- we expand that
        # into the richer saved format (sharp/flat alternatives, plus
        # dominant/subdominant/relative key) via build_expanded_key().
        key_of = song.get("key_of")
        if key_of:
            data["key_of"] = build_expanded_key(str(key_of).strip())
 
        # GetSongBPM reports these on a 0-100 scale; the original Spotify
        # fields were 0.0-1.0, so we rescale to match.
        danceability = song.get("danceability")
        if isinstance(danceability, (int, float)):
            data["danceability"] = round(danceability / 100.0, 3)
 
        acousticness = song.get("acousticness")
        if isinstance(acousticness, (int, float)):
            data["acousticness"] = round(acousticness / 100.0, 3)
 
        return True, data
 
    # Ran out of retries -- treat as "not found" for this track and move on.
    print("  [warning] Gave up on this track after repeated rate-limit responses.")
    return False, {}


# ==========================================================================
# STEP 4: PUTTING ONE ROW TOGETHER
# ==========================================================================

def build_row_for_track(api_key, music_dir, file_path):
    """Parses one file's path and looks it up on GetSongBPM, returning a
    finished CSV row (a dict)."""
    path_info = parse_track_path(music_dir, file_path)
    row = {column: "" for column in CSV_COLUMNS}
 
    # These three always get filled from the folder/file names, whether
    # or not GetSongBPM finds a match.
    row["path"] = path_info["relative_path"]
    row["artist"] = path_info["artist"]
    row["album"] = path_info["album"]
    row["track"] = path_info["track_title"]
 
    found, data = lookup_getsongbpm(api_key, path_info["artist"], path_info["track_title"])
 
    if not found:
        row["last_updated"] = "missing info"
        return row
 
    row["last_updated"] = datetime.now().strftime("%d.%m.%Y")
 
    if "tempo" in data:
        row["track_tempo"] = data["tempo"]
    if "key_of" in data:
        row["track_key"] = data["key_of"]
    if "time_signature" in data:
        row["track_timeSignature"] = data["time_signature"]
    if "danceability" in data:
        row["track_danceability"] = data["danceability"]
    if "acousticness" in data:
        row["track_acousticness"] = data["acousticness"]
 
    return row


# ==========================================================================
# STEP 5: MAIN PROGRAM - find all the files, loop through them, write the CSV
# ==========================================================================

def find_m4a_files(music_dir):
    """Returns a sorted list of every .m4a file under music_dir."""
    return sorted(music_dir.rglob("*.m4a"))


def main():
    parser = argparse.ArgumentParser(
        description="Log GetSongBPM tempo/key/mode/danceability/acousticness for every .m4a file in a music folder."
    )
    parser.add_argument("music_directory", help="Path to the top-level Music Directory folder.")
    args = parser.parse_args()
 
    music_dir = Path(args.music_directory).expanduser().resolve()
    if not music_dir.is_dir():
        sys.exit(f"ERROR: '{music_dir}' is not a folder that exists.")
 
    api_key = "" #getsongbpm API KEY <=================
    if not api_key:
        sys.exit(
            "ERROR: Please set the GETSONGBPM_API_KEY environment variable "
            "before running this script. Get a free key at "
            "https://getsongbpm.com/api"
        )
 
    csv_path = music_dir / CSV_FILENAME
    rows_by_path = load_existing_rows(csv_path)
 
    print("Scanning for .m4a files...")
    all_files = find_m4a_files(music_dir)
    print(f"Found {len(all_files)} .m4a file(s) total.")
 
    found_count = 0
    missing_count = 0
    skipped_count = 0
 
    for index, file_path in enumerate(all_files, start=1):
        # Log the moment this iteration (this one track) begins, and show
        # an updated progress bar for the overall run -- regardless of
        # whether this track ends up being skipped or actually looked up.
        step_started_at = datetime.now().strftime("%H:%M:%S")
        print(f"\n{format_progress_bar(index, len(all_files))}")

        path_info = parse_track_path(music_dir, file_path)
        relative_path = path_info["relative_path"]

        print(f"[{step_started_at}] [{index}/{len(all_files)}] {relative_path}")

        if row_is_complete(rows_by_path.get(relative_path)):
            skipped_count += 1
            print("  -> already logged, skipping.")
            continue

        calls_before = api_call_count
        row = build_row_for_track(api_key, music_dir, file_path)
 
        if row["last_updated"] == "missing info":
            missing_count += 1
            print("  -> not found on GetSongBPM.")
        else:
            found_count += 1
 
        # Update this one track's row and immediately re-save the whole
        # CSV, so progress is never lost if the script stops early.
        rows_by_path[relative_path] = row
        save_all_rows(csv_path, rows_by_path)

        # Only pause if this iteration actually spent a real API call on
        # GetSongBPM -- if lookup_getsongbpm bailed out early (e.g. a
        # network error before the request was ever sent), there's no
        # need to wait before moving on to the next track.
        if api_call_count > calls_before:
            print(f"API Fetch Count:{api_call_count}")
            time.sleep(2)
 
    print(f"\n{format_progress_bar(len(all_files), len(all_files))}")
    print("Done.")
    print(f"  Logged:        {found_count}")
    print(f"  Not found:     {missing_count}")
    print(f"  Skipped (already logged): {skipped_count}")
    print(f"CSV file: {csv_path}")
 
 
if __name__ == "__main__":
    main()
