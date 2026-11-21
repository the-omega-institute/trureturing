"""Load the installer from the SHA-256-pinned tools archive."""

import argparse
import fcntl
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
from urllib.request import urlopen


ROOT = Path(__file__).resolve().parents[2]
PIN = "Meta/tools-release.json"
RELEASES = "https://github.com/the-omega-institute/trureturing-tools/releases/download"
CACHE = ROOT / "build/tools-releases"


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
    if (set(pin) not in ({"version", "sha256"}, {"version", "sha256", "workflow_sha"})
            or ("workflow_sha" in pin and not re.fullmatch(r"[0-9a-f]{40}", pin["workflow_sha"]))
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


def release_member(archive, name):
    with tarfile.open(archive, "r:gz") as package:
        try:
            member = package.getmember(name)
        except KeyError:
            raise ValueError(
                f"release lacks {name}. Use the consumer revision paired with this older release."
            ) from None
        if not member.isfile():
            raise ValueError(f"invalid release member {name}")
        with package.extractfile(member) as source:
            return source.read()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, help="use a local copy of the pinned release asset")
    parser.add_argument("--cache-from", type=Path, help="reuse a matching release cached in this checkout")
    parser.add_argument("--cache-revision", help="cache this revision's tools without installing them")
    parser.add_argument("--read-makefile", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    pin = read_pin(args.cache_revision)
    if pin is None:
        return
    # A dry run verifies the existing installation without fetching or writing.
    if not args.read_makefile:
        CACHE.mkdir(parents=True, exist_ok=True)
    lock_mode = "rb" if args.read_makefile else "a"
    with (CACHE / "install.lock").open(lock_mode) as lock:
        fcntl.flock(lock, fcntl.LOCK_SH if args.read_makefile else fcntl.LOCK_EX)
        if args.read_makefile:
            archive = CACHE / (pin["sha256"] + ".tar.gz")
            if digest(archive) != pin["sha256"]:
                raise ValueError(f"SHA-256 mismatch for tools {pin['version']}")
        else:
            archive = cached_archive(pin, args.archive, args.cache_from)
        if args.cache_revision is None:
            program = release_member(archive, "tools/consumer/install.py")
            command = "read-makefile" if args.read_makefile else "install"
            result = subprocess.run(
                [sys.executable, "-I", "-B", "-", command, archive, pin["version"], pin["sha256"]],
                input=program, cwd=ROOT,
            )
            sys.exit(result.returncode)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError, tarfile.TarError, subprocess.CalledProcessError) as exc:
        sys.exit(f"tools release: {exc}")
