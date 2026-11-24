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
        blob = pin_blob(tree)
        if blob is None:
            return None
        data = git("cat-file", "blob", blob)
    return parse_pin(data)


def pin_blob(revision):
    entry = git("ls-tree", "--full-tree", revision, "--", PIN)
    if not entry:
        return None
    mode, kind, oid = entry.split(b"\t", 1)[0].decode().split()
    if kind != "blob" or mode not in {"100644", "100755"}:
        raise ValueError(f"{PIN} must be a regular file at {revision}")
    return oid


def unique_fields(pairs):
    fields = dict(pairs)
    if len(fields) != len(pairs):
        raise ValueError(f"duplicate field in {PIN}")
    return fields


def parse_pin(data):
    pin = json.loads(data, object_pairs_hook=unique_fields)
    if (not isinstance(pin, dict)
            or not {"version", "sha256"} <= pin.keys()
            or not pin.keys() <= {"version", "sha256", "workflow_sha", "source_sha", "previous_pin"}
            or not all(isinstance(value, str) for value in pin.values())
            or ("workflow_sha" in pin and not re.fullmatch(SHA, pin["workflow_sha"]))
            or ("previous_pin" in pin and not re.fullmatch(SHA, pin["previous_pin"]))
            or not re.fullmatch(r"v[0-9]+\.[0-9]+\.[0-9]+(?:-[0-9A-Za-z.-]+)?", pin["version"])
            or not re.fullmatch(r"[0-9a-f]{64}", pin["sha256"])):
        raise ValueError(f"invalid tools release pin in {PIN}")
    if "source_sha" in pin:
        preview = PR_PREVIEW.fullmatch(pin["version"])
        if not preview or not re.fullmatch(SHA, pin["source_sha"]) or not pin["source_sha"].startswith(preview[2]):
            raise ValueError(f"source_sha must be the full source of the PR preview in {PIN}")
    return pin


def github(*args):
    return json.loads(subprocess.check_output(["gh", "api", *args]))


def api(repo, endpoint, *, paginate=False):
    flags = ("--paginate", "--slurp") if paginate else ()
    return github(*flags, f"repos/{repo}/{endpoint}")


def pr_only_commits(repo, base, head):
    # GitHub Compare implements BASE..HEAD. Check the full paginated count
    # instead of using the shallow checkout's incomplete commit graph.
    pages = api(repo, f"compare/{base}...{head}?per_page=100", paginate=True)
    commits = [commit["sha"] for page in pages for commit in page["commits"]]
    if (not pages or any(page["base_commit"]["sha"] != base or page["ahead_by"] != len(commits)
                        for page in pages)
            or len(set(commits)) != len(commits)
            or (commits and head not in commits)
            or any(not re.fullmatch(SHA, commit) for commit in commits)):
        raise ValueError("incomplete consumer PR commit range")
    return commits


def verify_pin_history(repo, base, head, allowed):
    owner, name = map(json.dumps, repo.split("/"))
    commits = pr_only_commits(repo, base, head)
    for start in range(0, len(commits), 50):
        batch = commits[start:start + 50]
        queries = [
            f'c{i}:object(oid:"{commit}") {{ ... on Commit {{ oid file(path:"{PIN}") {{ oid mode }} '
            f'parents(first:100) {{ nodes {{ file(path:"{PIN}") {{ oid mode }} }} }} }} }}'
            for i, commit in enumerate(batch)
        ]
        query = f"{{ repository(owner:{owner},name:{name}) {{ {' '.join(queries)} }} }}"
        response = github("graphql", "-f", f"query={query}")
        if response.get("errors"):
            raise ValueError("could not inspect all consumer PR pin snapshots")
        snapshots = response["data"]["repository"]
        for i, commit in enumerate(batch):
            snapshot = snapshots[f"c{i}"]
            if snapshot is None or snapshot["oid"] != commit:
                raise ValueError(f"missing consumer PR commit {commit}")
            entry = snapshot["file"]
            blob = entry["oid"] if entry is not None else None
            # A content branch may inherit earlier dev pins as it merges dev.
            # Check every PR-only commit, so following a parent can never hide
            # the introduction of an unadopted third pin elsewhere in this DAG.
            inherited = any(parent["file"] == entry for parent in snapshot["parents"]["nodes"])
            if ((entry is not None and entry["mode"] not in {0o100644, 0o100755})
                    or (blob not in allowed and not inherited)):
                raise ValueError(f"tools pin conflict at consumer PR commit {commit}: "
                                 "rebase or condense the intermediate pin edits")


def verify_tools_ci(preview, source, pull):
    # The dev release producer checks the CI artifact's bytes. Here verify
    # that the matching source actually passed the test and package jobs.
    branch = pull["head"]["ref"]
    jobs_required = {
        "verify": "Run python3 .github/scripts/test-suites.py standalone",
        "package": "Run python3 package_release.py",
        **{f"Consumer fixture {i}": "Exercise candidate tools against the consumer fixture" for i in range(4)},
    }
    endpoint = f"actions/workflows/ci.yml/runs?head_sha={source}&status=success&per_page=100"
    for page in api(TOOLS, endpoint, paginate=True):
        for run in page["workflow_runs"]:
            if (run["path"] != ".github/workflows/ci.yml" or run["head_sha"] != source
                    or run["head_branch"] != branch
                    or (run["head_repository"] or {}).get("full_name") != pull["head"]["repo"]["full_name"]
                    or run["status"] != "completed" or run["conclusion"] != "success"
                    or run["event"] not in {"pull_request", "push", "workflow_dispatch"}):
                continue
            if run["event"] == "pull_request" and run["pull_requests"] and not any(
                str(pr["number"]) == preview[1] and pr["head"]["sha"] == source
                for pr in run["pull_requests"]
            ):
                continue
            jobs = api(TOOLS, f"actions/runs/{run['id']}/attempts/{run['run_attempt']}/jobs?per_page=100")["jobs"]
            completed_steps = {
                (job["name"], step["name"])
                for job in jobs if job["conclusion"] == "success"
                for step in job["steps"] if step["conclusion"] == "success"
            }
            if jobs_required.items() <= completed_steps:
                return
    raise ValueError(f"tools PR #{preview[1]} has no successful tools ci.yml test and package run at {source}")


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
            or not pull["head"]["repo"] or pull["head"]["sha"] != source
            or pull["draft"] or not (pull["state"] == "open" or (event == "push" and pull["merged"]))):
        raise ValueError(f"tools PR #{preview[1]} must target {TOOLS}/dev at the exact published head {source}")
    verify_tools_ci(preview, source, pull)


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


def verify_adoption(event, repo):
    base = git("rev-parse", "--verify", "HEAD^1").decode().strip()
    baseline = pin_blob(base)
    candidate = pin_blob("HEAD")
    changed = baseline != candidate
    pin = read_pin("HEAD")
    if pin is None:
        raise ValueError(f"missing {PIN} at HEAD")
    if changed and (baseline is None or pin.get("previous_pin") != baseline):
        raise ValueError(f"tools pin conflict: previous_pin must match the first parent's {PIN} blob "
                         f"({baseline}); refresh the pin and republish any paired preview")

    if event == "pull_request":
        head = git("rev-parse", "--verify", "HEAD^2").decode().strip()
        head_pin = pin_blob(head)
        if changed and head_pin != candidate:
            raise ValueError("the consumer PR head must carry the exact candidate tools pin")
        verify_pin_history(repo, base, head, {baseline, candidate})
        if not changed:
            return
        dev = api(repo, "git/ref/heads/dev")["object"]["sha"]
        if api(repo, f"contents/{PIN}?ref={dev}")["sha"] != baseline:
            raise ValueError("tools pin conflict: consumer dev changed its pin, refresh the pin "
                             "and republish any paired preview")

    verify_adopted_source(pin, baseline, read_pin(base), event, inherited=not changed)


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
    if args.verify_adopted_source and args.adoption_event:
        verify_adoption(args.adoption_event, os.environ.get("GITHUB_REPOSITORY", CONSUMER))
        return
    pin = read_pin(args.cache_revision)
    if pin is None:
        return
    if args.verify_adopted_source:
        verify_adopted_source(pin)
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
