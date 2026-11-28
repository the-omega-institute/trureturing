"""Install the tools release pinned by this checkout, or cache a historical pin."""

import argparse
import base64
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
TREE_MODE = 0o040000
REGULAR_MODES = {0o100644, 0o100755}
TREE_ENTRY_MODES = REGULAR_MODES | {TREE_MODE, 0o120000, 0o160000}
HISTORY_BATCH_SIZE = 50
HISTORY_PARENT_LIMIT = 100
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


def unique_fields(pairs, source=PIN):
    fields = dict(pairs)
    if len(fields) != len(pairs):
        raise ValueError(f"duplicate field in {source}")
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


def history_objects(repo, oids, selection):
    owner, name = map(json.dumps, repo.split("/"))
    queries = [f'o{i}:object(oid:"{oid}") {{ {selection} }}' for i, oid in enumerate(oids)]
    query = f"{{ repository(owner:{owner},name:{name}) {{ {' '.join(queries)} }} }}"
    response = github("graphql", "-f", f"query={query}")
    if "errors" in response:
        raise ValueError("could not inspect all consumer PR pin snapshots")
    objects = response["data"]["repository"]
    for i, oid in enumerate(oids):
        result = objects[f"o{i}"]
        if result is None or result.get("oid") != oid:
            raise ValueError(f"missing or mismatched consumer Git object {oid}")
        yield result


def complete_tree_entries(tree):
    entries = tree["entries"]
    if not isinstance(entries, list):
        raise ValueError(f"missing entries for consumer tree {tree['oid']}")
    by_name = {}
    for entry in entries:
        name = base64.b64decode(entry["nameRaw"], validate=True)
        mode, oid = entry["mode"], entry["oid"]
        if (not name or b"/" in name or b"\0" in name or name in {b".", b".."} or name in by_name
                or type(mode) is not int or mode not in TREE_ENTRY_MODES or not re.fullmatch(SHA, oid)):
            raise ValueError(f"malformed entries for consumer tree {tree['oid']}")
        by_name[name] = (oid, mode)

    # Tree.entries has no completeness flag. Rebuild the Git tree ID before
    # treating any omitted name as absent. Git sorts directories with a trailing slash.
    ordered = sorted(by_name.items(), key=lambda item: item[0] + (b"/" if item[1][1] == TREE_MODE else b""))
    body = b"".join(f"{mode:o} ".encode() + name + b"\0" + bytes.fromhex(oid) for name, (oid, mode) in ordered)
    if hashlib.sha1(f"tree {len(body)}\0".encode() + body).hexdigest() != tree["oid"]:
        raise ValueError(f"incomplete or inconsistent entries for consumer tree {tree['oid']}")
    return by_name


def load_history_trees(repo, oids, trees):
    missing = sorted(set(oids) - trees.keys())
    for start in range(0, len(missing), HISTORY_BATCH_SIZE):
        batch = missing[start:start + HISTORY_BATCH_SIZE]
        for tree in history_objects(repo, batch, "... on Tree { oid entries { nameRaw mode oid } }"):
            trees[tree["oid"]] = complete_tree_entries(tree)


def verify_pin_history(repo, base, head, allowed):
    commits = pr_only_commits(repo, base, head)
    root_by_commit = {}
    trees = {}
    directory, filename = PIN.encode().split(b"/")
    selection = ("... on Commit { oid tree { oid } "
                 f"parents(first:{HISTORY_PARENT_LIMIT}) "
                 "{ totalCount pageInfo { hasNextPage } nodes { oid tree { oid } } } }")
    for start in range(0, len(commits), HISTORY_BATCH_SIZE):
        batch = commits[start:start + HISTORY_BATCH_SIZE]
        parents_by_commit = {}
        for snapshot in history_objects(repo, batch, selection):
            commit = snapshot["oid"]
            parents = snapshot["parents"]
            nodes, count = parents["nodes"], parents["totalCount"]
            if (not isinstance(nodes, list) or type(count) is not int or len(nodes) != count
                    or count > HISTORY_PARENT_LIMIT
                    or parents["pageInfo"]["hasNextPage"] is not False):
                raise ValueError(f"incomplete consumer parents at {commit}")
            parents_by_commit[commit] = [parent["oid"] for parent in nodes]
            for node in [snapshot, *nodes]:
                revision, root = node["oid"], node["tree"]["oid"]
                if (not re.fullmatch(SHA, revision) or not re.fullmatch(SHA, root)
                        or root_by_commit.setdefault(revision, root) != root):
                    raise ValueError(f"invalid or inconsistent consumer commit tree at {revision}")

        revisions = batch + [parent for parents in parents_by_commit.values() for parent in parents]
        roots = {root_by_commit[revision] for revision in revisions}
        load_history_trees(repo, roots, trees)
        directories = {root: trees[root].get(directory) for root in roots}
        if any(entry is not None and entry[1] != TREE_MODE for entry in directories.values()):
            raise ValueError(f"parent directory of {PIN} must be a tree")
        load_history_trees(repo, (entry[0] for entry in directories.values() if entry is not None), trees)
        pins = {root: trees[entry[0]].get(filename) if entry is not None else None
                for root, entry in directories.items()}
        for revision in revisions:
            entry = pins[root_by_commit[revision]]
            if entry is not None and entry[1] not in REGULAR_MODES:
                raise ValueError(f"{PIN} must be a regular file at {revision}")

        for commit, parents in parents_by_commit.items():
            entry = pins[root_by_commit[commit]]
            blob = entry[0] if entry is not None else None
            # A content branch may inherit earlier dev pins as it merges dev.
            # Check every PR-only commit, so following a parent can never hide
            # the introduction of an unadopted third pin elsewhere in this DAG.
            inherited = any(pins[root_by_commit[parent]] == entry for parent in parents)
            if blob not in allowed and not inherited:
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


def omega_package_overrides(path):
    manifest = json.loads(path.read_bytes(), object_pairs_hook=lambda pairs: unique_fields(pairs, path))
    packages = manifest["packages"]
    if not isinstance(packages, list) or not all(isinstance(entry, dict) for entry in packages):
        raise ValueError(f"invalid package entries in {path}")
    entries = [entry for entry in packages if entry.get("name") == "omegamath"]
    if not entries:
        return None
    if len(entries) != 1 or manifest["version"] != "1.3.0":
        raise ValueError(f"expected one omegamath pin in a Lake 1.3.0 manifest: {path}")
    entry = entries[0]
    if (entry.get("type") != "git" or not isinstance(entry.get("rev"), str)
            or not re.fullmatch(SHA, entry["rev"]) or not isinstance(entry.get("url"), str)
            or not entry["url"]):
        raise ValueError(f"omegamath must have a full Git revision pin in {path}")
    # Installation precedes Lake's dependency checkout. The tool validator
    # checks the actual package revision and source when it consumes this pin.
    return {"version": "1.3.0", "packages": [entry | {"inherited": True}]}


def prepare_tool_overrides(overrides):
    content = None if overrides is None else (json.dumps(overrides, indent=1) + "\n").encode()
    for name in ("lean-inspector", "lean-inspector-reg", "lean-inspector-interface"):
        workspace = ROOT / "tools" / name
        destination = workspace / ".lake/package-overrides.json"
        if content is None:
            # A protected base may reuse a tools install from a newer checkout.
            destination.unlink(missing_ok=True)
            continue
        if not (workspace / "lake-manifest.json").is_file():
            raise ValueError(f"tools release is missing {workspace / 'lake-manifest.json'}")
        if destination.is_file() and not destination.is_symlink() and destination.read_bytes() == content:
            continue
        destination.parent.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=destination.parent) as tmp:
            staged = Path(tmp) / destination.name
            staged.write_bytes(content)
            os.replace(staged, destination)


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
            manifest = ROOT / "lake-manifest.json"
            # Sparse bootstrap jobs install tools without checking out Lean inputs.
            has_manifest = manifest.exists()
            overrides = omega_package_overrides(manifest) if has_manifest else None
            install(archive, pin)
            if has_manifest:
                prepare_tool_overrides(overrides)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError, tarfile.TarError, subprocess.CalledProcessError) as exc:
        sys.exit(f"tools release: {exc}")
