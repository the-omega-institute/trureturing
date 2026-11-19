"""Install the tools release pinned by this checkout, or cache a historical pin."""

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
from urllib.request import urlopen


ROOT = Path(__file__).resolve().parents[2]
PIN = "Meta/tools-release.json"
RELEASES = "https://github.com/the-omega-institute/trureturing-tools/releases/download"
CACHE = ROOT / "build/tools-releases"
STAMP = ".release-sha256"


def git(*args):
    return subprocess.check_output(["git", "-C", ROOT, *args])


def read_pin(revision):
    if revision is None:
        data = (ROOT / PIN).read_bytes()
    else:
        tree = git("rev-parse", "--verify", "--end-of-options", revision + "^{tree}").decode().strip()
        if not git("ls-tree", tree, "--", PIN):
            return None
        data = git("show", f"{tree}:{PIN}")
    pin = json.loads(data)
    if (set(pin) != {"version", "sha256"}
            or not re.fullmatch(r"v[0-9]+\.[0-9]+\.[0-9]+(?:-[0-9A-Za-z.-]+)?", pin["version"])
            or not re.fullmatch(r"[0-9a-f]{64}", pin["sha256"])):
        raise ValueError(f"invalid tools release pin in {PIN}")
    return pin


def digest(path):
    with path.open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def cached_archive(pin, supplied, donor):
    archive = CACHE / (pin["sha256"] + ".tar.gz")
    if supplied is None and archive.is_file() and digest(archive) == pin["sha256"]:
        return archive
    if supplied is None and donor is not None:
        source = donor / "build/tools-releases" / archive.name
        if source.is_file() and digest(source) == pin["sha256"]:
            supplied = source
    with tempfile.TemporaryDirectory(dir=CACHE) as tmp:
        download = Path(tmp) / "download"
        url = f"{RELEASES}/{pin['version']}/trureturing-tools.tar.gz"
        with (supplied.open("rb") if supplied else urlopen(url, timeout=60)) as src:
            with download.open("wb") as out:
                shutil.copyfileobj(src, out)
        if digest(download) != pin["sha256"]:
            raise ValueError(f"SHA-256 mismatch for tools {pin['version']}")
        download.replace(archive)
    return archive


def unpack(archive, stage):
    with tarfile.open(archive, "r:gz") as package:
        seen = set()
        for entry in package:
            parts = entry.name.split("/")
            if (parts[0] != "tools" or any(p in {"", ".", "..", ".git", STAMP} for p in parts)
                    or entry.name in seen or not (entry.isdir() or entry.isfile())):
                raise ValueError(f"unexpected tools archive entry {entry.name!r}")
            seen.add(entry.name)
            package.extract(entry, stage, filter="data")
        if not (stage / "tools/Makefile").is_file():
            raise ValueError("tools release is missing tools/Makefile")


def preserve_extra_files(entries):
    files = {Path(entry.name) for entry in entries if entry.isfile()}
    directories = {parent for path in files for parent in path.parents}
    project_dirs = {path.parent for path in files if path.suffix == ".csproj"}
    build_dirs = {parent / name for parent in project_dirs for name in ("bin", "obj")}
    build_dirs.update(path.parent / ".lake" for path in files
                      if path.name in {"lakefile.lean", "lakefile.toml"})
    python_caches = {path.parent / "__pycache__" for path in files if path.suffix == ".py"}
    generated = Path("tools/Generated/scribe-emissions.v1.json")
    directories.update(python_caches | {generated.parent})
    files.update({Path("tools") / STAMP, generated})

    backup = None
    pending = [Path("tools")]
    while pending:
        parent = pending.pop()
        for item in (ROOT / parent).iterdir():
            relative = parent / item.name
            if not item.is_symlink():
                if relative in directories and item.is_dir():
                    pending.append(relative)
                    continue
                if relative in build_dirs and item.is_dir():
                    continue
                if item.is_file() and (relative in files or
                                       (parent in python_caches and
                                        re.fullmatch(r".+\.pyc(?:\.[0-9]+)?", item.name))):
                    continue
            if backup is None:
                backup = Path(tempfile.mkdtemp(prefix="previous-", dir=CACHE))
                print(f"Preserving extra tools files at {backup}", file=sys.stderr)
            destination = backup / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            try:
                item.rename(destination)
            except FileNotFoundError:
                if os.path.lexists(item):
                    raise


def installation_matches(archive):
    with tarfile.open(archive, "r:gz") as package:
        preserve_extra_files(package.getmembers())
        for entry in package:
            if entry.isdir():
                continue
            path = ROOT / entry.name
            try:
                info = path.lstat()
            except FileNotFoundError:
                return False
            if (not stat.S_ISREG(info.st_mode) or info.st_size != entry.size
                    or (info.st_mode & 0o111) != (entry.mode & 0o111)):
                return False
            with package.extractfile(entry) as expected, path.open("rb") as installed:
                if hashlib.file_digest(installed, "sha256").digest() != hashlib.file_digest(expected, "sha256").digest():
                    return False
    return True


def install(archive, pin):
    target = ROOT / "tools"
    stamp = target / STAMP
    if target.is_symlink():
        raise ValueError(f"unexpected symbolic link at {target}")
    installed = stamp.read_text().strip() if stamp.is_file() else None
    if git("ls-files", "--", "tools"):
        raise ValueError("the checkout still tracks files under tools/")
    clean = False
    if installed and re.fullmatch(r"[0-9a-f]{64}", installed):
        previous_archive = CACHE / (installed + ".tar.gz")
        if installed == pin["sha256"]:
            clean = installation_matches(archive)
            if clean:
                return
        elif previous_archive.is_file() and digest(previous_archive) == installed:
            clean = installation_matches(previous_archive)
    with tempfile.TemporaryDirectory(dir=CACHE) as tmp:
        stage = Path(tmp)
        unpack(archive, stage)
        (stage / "tools" / STAMP).write_text(pin["sha256"] + "\n")
        previous = None
        if target.exists():
            # Retain local edits and installations with an unavailable manifest.
            previous = stage / "previous"
            if not clean:
                previous = Path(tempfile.mkdtemp(prefix="previous-", dir=CACHE)) / "tools"
            target.rename(previous)
        try:
            (stage / "tools").rename(target)
        except BaseException:
            if previous is not None:
                previous.rename(target)
            raise
        if previous is not None and not clean:
            print(f"Preserved the previous tools directory at {previous}", file=sys.stderr)
    print(f"Installed tools {pin['version']}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, help="use a local copy of the pinned release asset")
    parser.add_argument("--cache-from", type=Path, help="reuse a matching release cached in this checkout")
    parser.add_argument("--cache-revision", help="cache this revision's tools without installing them")
    args = parser.parse_args()
    pin = read_pin(args.cache_revision)
    if pin is None:
        return
    CACHE.mkdir(parents=True, exist_ok=True)
    with (CACHE / "install.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        archive = cached_archive(pin, args.archive, args.cache_from)
        if args.cache_revision is None:
            install(archive, pin)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError, tarfile.TarError, subprocess.CalledProcessError) as exc:
        sys.exit(f"tools release: {exc}")
