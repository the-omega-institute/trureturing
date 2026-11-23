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
CONSUMER = "the-omega-institute/trureturing"
TOOLS = "the-omega-institute/trureturing-tools"
RELEASES = f"https://github.com/{TOOLS}/releases/download"
CACHE = ROOT / "build/tools-releases"
STAMP = ".release-sha256"
SHA = r"[0-9a-f]{40}"
PR_PREVIEW = re.compile(r"v[0-9]+\.[0-9]+\.[0-9]+-pr\.([1-9][0-9]*)\.[1-9][0-9]*\.g([0-9a-f]{12})")
BASE_TRAILER = "consumer-tools-base"
ACTIONS_BOT = 41898282


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
    return parse_pin(data)


def parse_pin(data):
    pin = json.loads(data)
    if (not isinstance(pin, dict)
            or not {"version", "sha256"} <= pin.keys() <= {"version", "sha256", "workflow_sha", "source_sha"}
            or ("workflow_sha" in pin and not re.fullmatch(SHA, pin["workflow_sha"]))
            or not re.fullmatch(r"v[0-9]+\.[0-9]+\.[0-9]+(?:-[0-9A-Za-z.-]+)?", pin["version"])
            or not re.fullmatch(r"[0-9a-f]{64}", pin["sha256"])):
        raise ValueError(f"invalid tools release pin in {PIN}")
    if "source_sha" in pin:
        preview = PR_PREVIEW.fullmatch(pin["version"])
        if not preview or not re.fullmatch(SHA, pin["source_sha"]) or not pin["source_sha"].startswith(preview[2]):
            raise ValueError(f"source_sha must be the full source of the PR preview in {PIN}")
    return pin


def api(repo, endpoint):
    return json.loads(subprocess.check_output(["gh", "api", f"repos/{repo}/{endpoint}"]))


def tag_source(version, *, lightweight=False):
    ref = api(TOOLS, f"git/ref/tags/{version}")["object"]
    if not lightweight and ref["type"] == "tag":
        ref = api(TOOLS, f"git/tags/{ref['sha']}")["object"]
    if ref["type"] != "commit" or not re.fullmatch(SHA, ref["sha"]):
        raise ValueError(f"{version} must point to a tools commit")
    suffix = re.search(r"\.g([0-9a-f]{12}|[0-9a-f]{40})$", version)
    if suffix and not ref["sha"].startswith(suffix[1]):
        raise ValueError(f"{version} points to a different tools commit")
    return ref["sha"]


def contains(source, tip):
    return source == tip or api(TOOLS, f"compare/{source}...{tip}?per_page=1")["merge_base_commit"]["sha"] == source


def base_trailers(source):
    message = api(TOOLS, f"git/commits/{source}")["message"]
    trailers = subprocess.check_output(["git", "interpret-trailers", "--parse"], input=message, text=True)
    return [value.strip() for line in trailers.splitlines()
            for key, _, value in [line.partition(":")] if key.lower() == BASE_TRAILER]


def verify_paired(preview, source, baseline, previous, event):
    if baseline is None or previous is None:
        raise ValueError("verify a paired tools pin against the consumer commit's first-parent pin")
    trailers = base_trailers(source)
    if trailers != [baseline]:
        raise ValueError("tools pin conflict: integrate the current consumer pin source into the same tools PR, "
                         "prepare its new head, pass tools CI and publish a new preview")
    previous_source = tag_source(previous["version"])
    if previous.get("source_sha", previous_source) != previous_source or not contains(previous_source, source):
        raise ValueError("the tested tools PR head must contain the previous consumer pin source")
    pull = api(TOOLS, f"pulls/{preview[1]}")
    if (pull["base"]["ref"] != "dev" or pull["base"]["repo"]["full_name"] != TOOLS
            or (pull["head"]["repo"] or {}).get("full_name") != TOOLS or pull["head"]["sha"] != source
            or pull["draft"] or not (pull["state"] == "open" or (event == "push" and pull["merged"]))):
        raise ValueError(f"tools PR #{preview[1]} must target {TOOLS}/dev at the exact published head {source}")
    if event == "pull_request":
        dev = api(CONSUMER, "git/ref/heads/dev")["object"]["sha"]
        if api(CONSUMER, f"contents/{PIN}?ref={dev}")["sha"] != baseline:
            raise ValueError("tools pin conflict: consumer dev changed its pin, prepare and publish a new tools PR head")


def verify_adopted_source(pin, baseline=None, previous=None, event=None, *, inherited=False):
    version = pin["version"]
    preview = "-" in version
    branch = "dev" if preview else "main"
    metadata = api(TOOLS, f"releases/tags/{version}")
    assets = [asset for asset in metadata["assets"] if asset["name"] == "trureturing-tools.tar.gz"]
    if (metadata["tag_name"] != version or metadata["draft"] or metadata["prerelease"] != preview
            or len(assets) != 1 or assets[0]["state"] != "uploaded" or assets[0]["digest"] != "sha256:" + pin["sha256"]):
        raise ValueError(f"{version} does not match the published tools archive and checksum")
    pr_preview = PR_PREVIEW.fullmatch(version)
    source = tag_source(version, lightweight="source_sha" in pin)
    if "source_sha" in pin:
        if (source != pin["source_sha"] or metadata["author"]["id"] != ACTIONS_BOT
                or assets[0]["uploader"]["id"] != ACTIONS_BOT):
            raise ValueError(f"{version} must be an Actions publication at the pinned full source SHA")
        if inherited:
            return  # A push batch ends after the transition. Delivery verifies the actual merge.
        verify_paired(pr_preview, source, baseline, previous, event)
        print(f"Verified paired tools PR #{pr_preview[1]} at {source}")
        return
    if pr_preview and base_trailers(source):
        raise ValueError(f"pin the full source_sha of paired preview {version}")
    if not contains(source, branch):
        raise ValueError(f"merge the source of {version} into trureturing-tools/{branch} or pin a paired preview")
    print(f"Verified tools {version} at {source} on {TOOLS}/{branch}")


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
            try:
                mode = item.lstat().st_mode
            except FileNotFoundError:
                continue
            if stat.S_ISDIR(mode):
                if relative in directories:
                    pending.append(relative)
                    continue
                if relative in build_dirs:
                    continue
            if stat.S_ISREG(mode):
                bytecode = parent in python_caches and re.fullmatch(r".+\.pyc(?:\.[0-9]+)?", item.name)
                if relative in files or bytecode:
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
    parser.add_argument("--verify-adopted-source", action="store_true", help="verify the published pin and upstream source for downstream dev")
    parser.add_argument("--adoption-event", choices=("pull_request", "push"), help="verify the checked-out GitHub merge or push snapshot")
    args = parser.parse_args()
    pin = read_pin(args.cache_revision)
    if pin is None:
        return
    if args.verify_adopted_source:
        baseline = previous = None
        inherited = False
        if args.adoption_event:
            previous = read_pin("HEAD^1")
            if previous is not None:
                baseline = git("rev-parse", f"HEAD^1:{PIN}").decode().strip()
                inherited = baseline == git("rev-parse", f"HEAD:{PIN}").decode().strip()
        if not inherited or args.adoption_event == "push":
            verify_adopted_source(pin, baseline, previous, args.adoption_event, inherited=inherited)
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
