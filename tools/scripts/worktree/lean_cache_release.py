"""Optional, immutable Release snapshots; never a check verdict or a source selector."""
from __future__ import annotations

import argparse
import contextlib
import datetime
import hashlib
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time
from urllib.parse import quote

from lean_cache import SHARED_SEED_PLATFORMS, normalized_platform, partition_path, seed_partitions
from cache_material import sha

# Use the report entry's declared format and execution capture, never program hashes.
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "lean-inspector"))
import reuse as report_reuse

ASSET = "lean-build.tgz"
MANIFEST = "manifest.json"
REPO = os.environ.get("STRATALINT_CACHE_REPO", "the-omega-institute/trureturing")
# Issue #6194, run 34119746844: Release assets must be strictly below 2 GiB.
# Keep dev's 1.5 GiB headroom and two-digit, at-most-100-part inventory.
CHUNK_BYTES = 1610612736
# Optional transport policy (#5985): a thirty-minute operation ceiling,
# configurable downward, leaves headroom over measured multipart Release fetches
# of the 4 GB seed on a developer host (5m08s, #2634; 7m09s for one fetch, and
# over ten minutes when two fetches share the link). This is a policy choice,
# not a throughput derivation or a copy of the C# ArchiveBudget.
# Fetch includes all snapshot attempts; publish starts only after the current report succeeds.
RELEASE_OPERATION_TIMEOUT_SECONDS = 1800


def operation_deadline():
    variable = "STRATALINT_LEAN_CACHE_RELEASE_TIMEOUT_SECONDS"
    try:
        seconds = int(os.environ.get(variable, str(RELEASE_OPERATION_TIMEOUT_SECONDS)))
        if not 0 < seconds <= RELEASE_OPERATION_TIMEOUT_SECONDS:
            raise ValueError()
    except ValueError:
        raise ValueError(f"{variable} must be 1..{RELEASE_OPERATION_TIMEOUT_SECONDS}") from None
    return time.monotonic() + seconds


def remaining(deadline):
    seconds = deadline - time.monotonic()
    if seconds <= 0:
        raise TimeoutError("Release operation deadline exhausted")
    return seconds


class ArchiveOutput:
    """Check the publication budget at each bounded tar/gzip output write."""
    def __init__(self, output, deadline):
        self.output, self.deadline = output, deadline

    def __getattr__(self, name):
        return getattr(self.output, name)

    def write(self, block):
        remaining(self.deadline)
        count = self.output.write(block)
        remaining(self.deadline)
        return count


def archive_sha(path, deadline):
    value = hashlib.sha256()
    with path.open("rb") as source:
        while True:
            remaining(deadline)
            block = source.read(1024 * 1024)
            if not block:
                return value.hexdigest()
            value.update(block)


class GitHubCommandError(subprocess.CalledProcessError):
    """Keep captured diagnostics in callers' failure receipts."""
    def __str__(self):
        return f"{super().__str__()} stderr: {self.stderr or '<empty>'}"


def checked_run(command, deadline):
    try:
        return subprocess.run(command, check=True, capture_output=True, text=True,
                              timeout=remaining(deadline))
    except subprocess.CalledProcessError as error:
        raise GitHubCommandError(error.returncode, error.cmd,
                                 output=error.output, stderr=error.stderr) from error


def gh(deadline, *args):
    return checked_run(["gh", *args], deadline).stdout


def receipt(verb, status, **fields):
    print("LEAN_CACHE_" + verb.upper() + " " + json.dumps({"status": status, **fields}, separators=(",", ":")))


def existing_release(tag, deadline):
    """Return exact release metadata, or None when the tag is absent."""
    try:
        raw = gh(deadline, "api", f"repos/{REPO}/releases/tags/{tag}")
    except GitHubCommandError as error:
        # gh uses the same nonzero exit for missing tags and transport/API
        # errors. Only GitHub's explicit 404 response permits a create attempt.
        try:
            failure = json.loads(error.output)
        except (TypeError, json.JSONDecodeError):
            raise error
        if isinstance(failure, dict) and failure.get("status") == "404":
            return None
        raise
    try:
        metadata = json.loads(raw)
    except (TypeError, json.JSONDecodeError) as error:
        raise ValueError(f"exact release {tag} returned malformed metadata: {error}") from error
    if not isinstance(metadata, dict) or type(metadata.get("draft")) is not bool:
        raise ValueError(f"exact release {tag} returned malformed metadata: expected boolean draft")
    if metadata.get("tag_name") != tag:
        raise ValueError(f"exact release {tag} returned malformed metadata: tag mismatch")
    return metadata


def partition_prefix(partition, verification=False):
    namespace = "lean-cache-verify-v1-" if verification else "lean-cache-v2-"
    return namespace + partition.replace("/", "-") + "-"


def release_key(root, captured=None):
    """Project the report receipt's explicit execution onto the seed platform family."""
    captured = report_reuse.capture(root) if captured is None else captured
    if not captured['eligible']:
        raise ValueError("Release key requires registered execution: " + captured['reason'])
    execution = captured['execution']
    system, machine = normalized_platform(execution['platform']['system'], execution['platform']['machine'])
    platform_name = system + "-" + machine
    family = next((group for group in SHARED_SEED_PLATFORMS if platform_name in group), (platform_name,))
    projection = dict(toolchain=(root / execution['toolchain']).read_text(encoding='utf-8').strip(),
        tools=sorted(execution['tools']), platform="+".join(sorted(family)),
        environment=execution['environment'])
    digest = hashlib.sha256(json.dumps(projection, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return dict(report_format=report_reuse.publication.selection.REPORT_FORMAT, execution_sha256=digest)


def prefix(partition, cache_key, verification=False):
    return (partition_prefix(partition, verification) + "report-" + cache_key['report_format']
            + "-env-" + cache_key['execution_sha256'][:12] + "-")


def validate_source_ref(repo, source_ref, source_commit, api):
    def commit(value):
        if not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{40}", value) or value == "0" * 40:
            raise ValueError("source commit must be a nonzero immutable 40-hex SHA")
        return value

    commit(source_commit)
    if (not isinstance(source_ref, str) or not source_ref.startswith("refs/heads/")
            or subprocess.run(["git", "check-ref-format", source_ref], capture_output=True).returncode != 0):
        raise ValueError("source ref must be a full branch ref")
    branch = source_ref.removeprefix("refs/heads/")
    prefix = "repos/" + repo + "/"
    source = api(prefix + "branches/" + quote(branch, safe=""))
    if not isinstance(source, dict) or source.get("name") != branch or source.get("protected") is not True:
        raise ValueError("source branch is not protected or its identity differs")
    if not isinstance(source.get("commit"), dict):
        raise ValueError("source branch snapshot is missing its commit")
    tip = commit(source["commit"].get("sha"))
    comparison = api(prefix + "compare/" + source_commit + "..." + tip)
    if (not isinstance(comparison, dict) or comparison.get("status") not in ("ahead", "identical")
            or not isinstance(comparison.get("merge_base_commit"), dict)
            or comparison["merge_base_commit"].get("sha") != source_commit):
        raise ValueError("source commit is not on the protected branch snapshot")
    return branch


def verification_identity(root, source_ref, source_commit, deadline):
    run, attempt = (os.environ.get(field, "") for field in ("GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT"))
    if (os.environ.get("GITHUB_ACTIONS") != "true" or os.environ.get("GITHUB_EVENT_NAME") != "push"
            or not source_ref.startswith("refs/heads/integration-")
            or os.environ.get("GITHUB_REF") != source_ref or os.environ.get("GITHUB_SHA") != source_commit
            or os.environ.get("GITHUB_REPOSITORY") != REPO
            or not re.fullmatch(r"[0-9a-f]{40}", source_commit)
            or not all(re.fullmatch(r"[1-9][0-9]*", value) for value in (run, attempt))):
        raise ValueError("verification requires a native integration push with explicit matching source and run attribution")
    head = checked_run(["git", "-C", str(root), "rev-parse", "--verify", "HEAD"], deadline).stdout.strip()
    dirty = checked_run(["git", "-C", str(root), "status", "--porcelain", "--untracked-files=no"], deadline).stdout
    if head != source_commit or dirty:
        raise ValueError("verification requires the clean fixed source checkout")
    request = lambda path: json.loads(gh(deadline, "api", path))
    branch = validate_source_ref(REPO, source_ref, source_commit, request)
    record = request(f"repos/{REPO}/actions/runs/{run}/attempts/{attempt}")
    if (not isinstance(record, dict) or type(record.get("id")) is not int or record["id"] != int(run)
            or type(record.get("run_attempt")) is not int or record["run_attempt"] != int(attempt)
            or record.get("event") != "push" or record.get("head_sha") != source_commit
            or record.get("head_branch") != branch or not isinstance(record.get("repository"), dict)
            or record["repository"].get("full_name") != REPO):
        raise ValueError("verification run does not match the native push source and attempt")
    return {"producer_commit_sha": source_commit, "workflow_run_id": run,
            "workflow_run_attempt": attempt, "source_ref": source_ref}


def publication_identity(root, deadline, verification=None):
    """Bind the snapshot to clean protected-branch content; suffixes only disambiguate writes."""
    commit = checked_run(["git", "-C", str(root), "rev-parse", "--verify", "HEAD"], deadline).stdout.strip()
    dirty = checked_run(["git", "-C", str(root), "status", "--porcelain"], deadline).stdout
    if dirty:
        raise ValueError("snapshot publication requires a clean working tree")
    if verification is None:
        request = lambda path: json.loads(gh(deadline, "api", path))
        validate_source_ref(REPO, "refs/heads/dev", commit, request)
    elif commit != verification['producer_commit_sha']:
        raise ValueError("verification source changed during the build")
    identity = dict(producer_commit_sha=commit)
    if verification is not None or os.environ.get("GITHUB_ACTIONS") == "true":
        run, attempt = (os.environ.get(field, "") for field in ("GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT"))
        if not all(re.fullmatch(r"[1-9][0-9]*", value) for value in (run, attempt)):
            raise ValueError("CI snapshot suffix requires a run ID and attempt")
        identity.update(workflow_run_id=run, workflow_run_attempt=attempt, publication_id="ci-" + run + "-" + attempt)
    else:
        stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
        identity['publication_id'] = "local-" + commit[:12] + "-" + stamp
    if verification is not None:
        identity.update(verification)
    return identity


def valid_publication_id(value):
    return isinstance(value, str) and re.fullmatch(
        r"ci-[1-9][0-9]*-[1-9][0-9]*|local-[0-9a-f]{12}-[0-9]{8}T[0-9]{12}Z", value) is not None


def archive_parts(stage, deadline):
    archive = stage / ASSET
    size = archive.stat().st_size
    count = (size + CHUNK_BYTES - 1) // CHUNK_BYTES
    if not 1 <= count <= 100:
        raise ValueError("archive must fit in 1 to 100 parts")
    paths = [archive]
    if count > 1:
        paths = []
        with archive.open("rb") as source:
            for index in range(count):
                path = stage / f"{ASSET}.part-{index:02d}"
                bytes_left = min(CHUNK_BYTES, size - index * CHUNK_BYTES)
                with path.open("wb") as target:
                    while bytes_left:
                        remaining(deadline)
                        block = source.read(min(bytes_left, 1024 * 1024))
                        if not block:
                            raise ValueError("archive ended before its declared size")
                        target.write(block)
                        bytes_left -= len(block)
                paths.append(path)
    return [{"name": path.name, "sha256": archive_sha(path, deadline), "bytes": path.stat().st_size} for path in paths]


def declared_parts(manifest, maximum_bytes=CHUNK_BYTES):
    parts = manifest.get("parts")
    if not isinstance(parts, list) or not 1 <= len(parts) <= 100:
        raise ValueError("invalid archive parts inventory")
    for index, part in enumerate(parts):
        name = ASSET if len(parts) == 1 else f"{ASSET}.part-{index:02d}"
        if (not isinstance(part, dict) or set(part) != {"name", "sha256", "bytes"}
                or part["name"] != name or not isinstance(part["sha256"], str)
                or not re.fullmatch(r"[0-9a-f]{64}", part["sha256"])
                or type(part["bytes"]) is not int or not 0 < part["bytes"] <= maximum_bytes):
            raise ValueError("invalid archive parts inventory")
    if (type(manifest.get("archive_bytes")) is not int
            or sum(part["bytes"] for part in parts) != manifest["archive_bytes"]):
        raise ValueError("archive byte count does not match its parts")
    return parts


def prune(partition, tag, deadline):
    pruned = 0
    try:
        releases = json.loads(gh(deadline, "release", "list", "--repo", REPO, "--limit", "100",
            "--json", "tagName,createdAt,isDraft"))
        if not isinstance(releases, list) or any(not isinstance(item, dict)
                or not isinstance(item.get("tagName"), str) or not isinstance(item.get("createdAt"), str)
                or not isinstance(item.get("isDraft"), bool) for item in releases):
            raise ValueError("snapshot cleanup metadata is malformed; pruned nothing")
        snapshots = sorted((item for item in releases if item.get("isDraft") is False
            and item.get("tagName", "").startswith(partition_prefix(partition))),
            key=lambda item: item["createdAt"], reverse=True)
        # Preserve the existing five-snapshot retention window, now per partition.
        for old in snapshots[5:]:
            if old["tagName"] == tag:
                continue
            gh(deadline, "release", "delete", old["tagName"], "--repo", REPO, "--yes", "--cleanup-tag")
            pruned += 1
        return pruned, None
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        return pruned, str(error)


@contextlib.contextmanager
def cache_guard(root, shared=False):
    # Same POSIX lock protocol as LeanCacheGuard. Snapshot reads share ownership;
    # direct restores require exclusive ownership of the private target.
    import fcntl
    directory = pathlib.Path.home() / ".cache/stratalint-lean-cache-guards"
    directory.mkdir(parents=True, exist_ok=True)
    address = hashlib.sha256(str((root / ".lake").resolve()).encode()).hexdigest()
    with (directory / (address + ".lock")).open("a+b") as lock:
        fcntl.flock(lock, (fcntl.LOCK_SH if shared else fcntl.LOCK_EX) | fcntl.LOCK_NB)
        yield


def publish(root, partition, verification=None):
    # Build/content failures remain failures. Production transport is optional;
    # explicit verification succeeds only after the uploaded bytes restore.
    # A caller's LEAN_REPORT override must not move publication outside buildDir.
    build = subprocess.run(["make", "lean-report",
        "LEAN_REPORT=.lake/build/stratalint/raw-lean-report.json"], cwd=root)
    if build.returncode:
        return build.returncode
    report = root / ".lake/build/stratalint/raw-lean-report.json"
    content_validated = False
    try:
        deadline = operation_deadline()
        with tempfile.TemporaryDirectory(prefix="lean-release-") as temporary:
            stage = pathlib.Path(temporary)
            # Validate and pack under one read lock so a cache writer cannot
            # replace the validated report/build before the snapshot is packed.
            with cache_guard(root, shared=True):
                if (root / ".lake").is_symlink() or not (root / ".lake/build").is_dir():
                    raise ValueError("no private project build to publish")
                captured = report_reuse.capture(root)
                report_reuse.read_receipt(report, captured)
                report_reuse.publication.validate_bundle(report, repository=root)
                if partition != partition_path(root):
                    raise ValueError("publication partition differs from the local tree")
                cache_key = release_key(root, captured)
                identity = publication_identity(root, deadline, verification)
                content_validated = True
                tag = prefix(partition, cache_key, verification is not None) + identity['publication_id']
                existing = existing_release(tag, deadline)
                if existing is not None:
                    if existing["draft"]:
                        raise ValueError(f"exact release {tag} is an incomplete draft; refusing to modify it")
                    if verification is not None:
                        raise ValueError(f"verification release {tag} already exists; refusing to replace it")
                    snapshot_manifest(partition, tag, stage, deadline,
                                      expected=identity, metadata=existing, cache_key=cache_key)
                    receipt("publish", "exists", tag=tag, release_target=existing.get("target_commitish"), **identity)
                    return 0
                # Level 1 keeps the gzip protocol within the transport window.
                with (stage / ASSET).open("wb") as output:
                    with tarfile.open(stage / ASSET, "w:gz", compresslevel=1,
                                      fileobj=ArchiveOutput(output, deadline)) as archive:
                        archive.add(root / ".lake/build", arcname="build")
            metadata = {"schema": "lean-release-seed-v4", "partition": partition, "cache_key": cache_key,
                **identity,
                "archive_sha256": archive_sha(stage / ASSET, deadline), "archive_bytes": (stage / ASSET).stat().st_size,
                "parts": archive_parts(stage, deadline)}
            (stage / MANIFEST).write_text(json.dumps(metadata, sort_keys=True) + "\n")
            # Never clobber an existing snapshot. Failed/racing publishers leave
            # at most a draft, which fetch never considers an applicable seed.
            # The server's default branch anchors only the storage container.
            gh(deadline, "release", "create", tag, "--repo", REPO, "--draft",
               "--title", "Lean cache " + partition, "--notes", "Successful current Lean build and Inspector report; incremental seed only.")
            gh(deadline, "release", "upload", tag, *(str(stage / part["name"]) for part in metadata["parts"]),
               str(stage / MANIFEST), "--repo", REPO)
            gh(deadline, "release", "edit", tag, "--repo", REPO, "--draft=false")
            if verification is not None:
                # Verify this exact inventory through restore into an empty target.
                target, downloaded = stage / "verified-target", stage / "downloaded"
                target.mkdir()
                downloaded.mkdir()
                restore_snapshot(target, partition, tag, downloaded, deadline, metadata, cache_key=cache_key)
                pruned, prune_error = 0, None
            else:
                current = existing_release(tag, deadline)
                if current is None or current["draft"]:
                    raise ValueError(f"new snapshot {tag} is not readable as published; pruned nothing")
                confirmed = stage / "confirmed"
                confirmed.mkdir()
                snapshot_manifest(partition, tag, confirmed, deadline, expected=metadata, metadata=current, cache_key=cache_key)
                pruned, prune_error = prune(partition, tag, deadline)
            receipt("publish", "published", tag=tag, pruned=pruned, prune_error=prune_error, **metadata)
    except ImportError as error:
        receipt("publish", "skipped", reason="POSIX cache locking unavailable: " + str(error))
        return 1 if verification is not None else 0
    except report_reuse.INVALID_SEED + (EOFError, subprocess.SubprocessError, tarfile.TarError) as error:
        receipt("publish", "failed", reason=str(error))
        return 1 if verification is not None else (0 if content_validated else 2)
    return 0


def snapshot_manifest(partition, tag, stage, deadline, expected=None, verification=False, metadata=None, *, cache_key):
    """Validate the small manifest and inventory before confirming or restoring a snapshot."""
    if metadata is None:
        metadata = json.loads(gh(deadline, "api", f"repos/{REPO}/releases/tags/{tag}"))
    if not isinstance(metadata, dict) or metadata.get("draft") is not False or metadata.get("tag_name") != tag:
        raise ValueError("snapshot is not published")
    manifest_name = MANIFEST
    assets = metadata.get("assets", [])
    if (not isinstance(assets, list) or any(not isinstance(asset, dict)
            or not isinstance(asset.get("name"), str) for asset in assets)
            or len({asset["name"] for asset in assets}) != len(assets)):
        raise ValueError("snapshot asset set is incomplete")
    recorded = {asset["name"]: asset.get("digest") for asset in assets}
    gh(deadline, "release", "download", tag, "--repo", REPO, "--dir", str(stage),
       "--pattern", manifest_name)
    if recorded.get(manifest_name) != "sha256:" + sha(stage / manifest_name):
        raise ValueError("transferred asset digest mismatch")
    manifest = report_reuse.publication.read_json((stage / manifest_name).read_bytes())
    if not isinstance(manifest, dict):
        raise ValueError("snapshot manifest must be an object")
    commit, publication_id = manifest.get("producer_commit_sha", ""), manifest.get("publication_id", "")
    if (manifest.get("schema") != "lean-release-seed-v4" or manifest.get("partition") != partition
            or manifest.get("cache_key") != cache_key
            or not isinstance(commit, str) or not re.fullmatch(r"[0-9a-f]{40}", commit)
            or not valid_publication_id(publication_id)
            or tag != prefix(partition, cache_key, verification) + publication_id):
        raise ValueError("snapshot partition or source attribution mismatch")
    if publication_id.startswith("ci-"):
        run, attempt = manifest.get("workflow_run_id"), manifest.get("workflow_run_attempt")
        if (not all(isinstance(value, str) and re.fullmatch(r"[1-9][0-9]*", value) for value in (run, attempt))
                or publication_id != f"ci-{run}-{attempt}"):
            raise ValueError("snapshot partition or source attribution mismatch")
    else:
        if publication_id.split("-")[1] != commit[:12]:
            raise ValueError("snapshot partition or source attribution mismatch")
        datetime.datetime.strptime(publication_id.split("-")[2], "%Y%m%dT%H%M%S%fZ")
    if expected is not None and any(manifest.get(key) != value for key, value in expected.items()):
        raise ValueError("snapshot does not match this exact publication")
    parts = declared_parts(manifest)
    if sorted(recorded) != sorted([manifest_name, *[part["name"] for part in parts]]):
        raise ValueError("snapshot asset set is incomplete")
    assets_by_name = {asset["name"]: asset for asset in assets}
    for part in parts:
        asset = assets_by_name[part["name"]]
        if asset.get("digest") != "sha256:" + part["sha256"]:
            raise ValueError("transferred asset digest mismatch")
        if type(asset.get("size")) is not int or asset["size"] != part["bytes"]:
            raise ValueError("transferred asset size mismatch")
    return metadata, manifest, parts


def restore_snapshot(root, partition, tag, stage, deadline, verification=None, refresh_stale=False, *, cache_key):
    metadata, manifest, parts = snapshot_manifest(partition, tag, stage, deadline,
        expected=verification, verification=verification is not None, cache_key=cache_key)
    assets = metadata["assets"]
    commit = manifest["producer_commit_sha"]
    gh(deadline, "release", "download", tag, "--repo", REPO, "--dir", str(stage),
       *(argument for part in parts for argument in ("--pattern", part["name"])))
    for part in parts:
        path = stage / part["name"]
        if part["sha256"] != sha(path) or part["bytes"] != path.stat().st_size:
            raise ValueError("part checksum or size mismatch: " + part["name"])
    for asset in assets:
        if asset.get("digest") != "sha256:" + sha(stage / asset["name"]):
            raise ValueError("transferred asset digest mismatch")
    if len(parts) > 1:
        with (stage / ASSET).open("wb") as archive:
            for part in parts:
                with (stage / part["name"]).open("rb") as source:
                    shutil.copyfileobj(source, archive, length=1024 * 1024)
    if (manifest.get("archive_sha256") != sha(stage / ASSET)
            or manifest.get("archive_bytes") != (stage / ASSET).stat().st_size):
        raise ValueError("archive checksum or size mismatch")
    lake = root / ".lake"
    if lake.is_symlink():
        raise ValueError("shared cache target is forbidden")
    installed = []
    with tarfile.open(stage / ASSET) as archive:
        members = archive.getmembers()
        paths = {}
        for member in members:
            path = pathlib.PurePosixPath(member.name)
            if (path.is_absolute() or ".." in path.parts or not path.parts
                    or path.parts[0] != "build"
                    or not (member.isfile() or member.isdir())):
                raise ValueError("archive contains an invalid cache member")
            if path in paths:
                raise ValueError("archive contains an invalid cache member: duplicate path")
            paths[path] = member
        for path in paths:
            if any(parent in paths and not paths[parent].isdir() for parent in path.parents):
                raise ValueError("archive contains an invalid cache member: file ancestor")
        # Tar's end marker precedes gzip's footer. Consume the remainder so a
        # truncated/corrupt compressed stream cannot be installed as complete.
        while archive.fileobj.read(1024 * 1024):
            remaining(deadline)
        lake.mkdir(exist_ok=True)
        # Stage on the destination filesystem so installation only renames the
        # verified directories, without allocating a second unpacked build.
        with tempfile.TemporaryDirectory(prefix=".release-", dir=lake) as temporary:
            unpacked = pathlib.Path(temporary)
            # A truncated archive cannot reach the installed cache directories.
            archive.extractall(unpacked, members=members)
            if not (unpacked / "build").is_dir():
                raise ValueError("archive has no project build")
            remaining(deadline)
            for name in ("build",):
                source, target = unpacked / name, lake / name
                if not source.is_dir() or target.is_symlink():
                    continue
                if target.exists() and (not target.is_dir() or (not refresh_stale and any(target.iterdir()))):
                    continue
                (source / ".release-refreshed-at").write_text(
                    datetime.datetime.now(datetime.timezone.utc).isoformat() + "\n", encoding="utf-8")
                # Keep the old tree until the validated replacement is in place.
                # A failed rollback retains its backup outside staging cleanup.
                backup = None
                if target.is_dir():
                    backup = pathlib.Path(tempfile.mkdtemp(prefix=".release-backup-", dir=lake))
                    try:
                        target.rename(backup / name)
                    except BaseException:
                        backup.rmdir()
                        raise
                try:
                    source.rename(target)
                except BaseException:
                    if backup is not None:
                        (backup / name).rename(target)
                        backup.rmdir()
                    raise
                installed.append(name)
                if backup is not None:
                    shutil.rmtree(backup)
    receipt("fetch", "unpacked" if installed else "skipped",
            mode="verification" if verification is not None else "partition", resolved=tag,
            installed=installed,
            producer_commit_sha=commit, publication_id=manifest["publication_id"], partition=partition,
            **{key: manifest[key] for key in ("workflow_run_id", "workflow_run_attempt") if key in manifest},
            release_target=metadata.get("target_commitish"))


def fetch_verification(root, partition, identity):
    cache_key = release_key(root)
    tag = prefix(partition, cache_key, True) + "ci-" + identity["workflow_run_id"] + "-" + identity["workflow_run_attempt"]
    try:
        deadline = operation_deadline()
        with cache_guard(root), tempfile.TemporaryDirectory(prefix="lean-fetch-verify-") as temporary:
            restore_snapshot(root, partition, tag, pathlib.Path(temporary), deadline, identity, cache_key=cache_key)
        return 0
    except (OSError, EOFError, ImportError, ValueError, KeyError, TypeError, subprocess.SubprocessError, tarfile.TarError) as error:
        receipt("fetch", "miss", mode="verification", reason=str(error), resolved=tag, partition=partition)
        return 1


def fetch(root, partition, writer_owned=False, refresh_stale=False):
    if os.environ.get("GITHUB_ACTIONS") == "true":
        receipt("fetch", "skipped", reason="CI does not consume Release seeds")
        return 0
    if os.environ.get("STRATALINT_ACTIONS_CACHE_SEEDED", "").lower() in ("1", "true"):
        receipt("fetch", "skipped", reason="Actions supplied an applicable seed")
        return 0
    try:
        deadline = operation_deadline()
        with contextlib.nullcontext() if writer_owned else cache_guard(root):
            return fetch_locked(root, partition, deadline, refresh_stale)
    except (OSError, ImportError, ValueError) as error:
        receipt("fetch", "miss", reason=str(error), partition=partition)
        return 1


def fetch_locked(root, partition, deadline, refresh_stale=False):
    reason = "no published snapshot in this partition"
    compatible = [partition] + [other for other in seed_partitions(root) if other != partition]
    cache_key = release_key(root)
    try:
        releases = json.loads(gh(deadline, "release", "list", "--repo", REPO, "--limit", "100",
            "--json", "tagName,createdAt,isDraft"))
        for release in sorted(releases, key=lambda item: item["createdAt"], reverse=True):
            tag = release.get("tagName", "")
            source = next((candidate for candidate in compatible
                if tag.startswith(prefix(candidate, cache_key))
                and valid_publication_id(tag[len(prefix(candidate, cache_key)):])), None)
            if release.get("isDraft") is not False or source is None:
                continue
            remaining(deadline)
            try:
                with tempfile.TemporaryDirectory(prefix="lean-fetch-") as temporary:
                    restore_snapshot(root, source, tag, pathlib.Path(temporary), deadline, refresh_stale=refresh_stale, cache_key=cache_key)
                return 0
            except (OSError, EOFError, ValueError, KeyError, TypeError, subprocess.SubprocessError, tarfile.TarError) as error:
                reason = str(error)
                receipt("fetch", "miss", reason=reason, resolved=tag, partition=partition)
                if isinstance(error, (TimeoutError, subprocess.TimeoutExpired)):
                    break
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        reason = str(error)
    receipt("fetch", "miss", reason=reason, partition=partition)
    return 1


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("address", "publish", "fetch"))
    parser.add_argument("--repository", type=pathlib.Path, default=pathlib.Path(__file__).resolve().parents[3])
    parser.add_argument("--mode", choices=("production", "verification"), default="production")
    parser.add_argument("--source-ref", default="")
    parser.add_argument("--source-commit", default="")
    # Internal handoff from LeanArchiveFetch after its typed guard assertion.
    parser.add_argument("--writer-owned", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--refresh-stale", action="store_true",
                        help="replace an expired private project build after validating the complete snapshot")
    args = parser.parse_args()
    try:
        if args.refresh_stale and (args.command != "fetch" or args.mode != "production"):
            raise ValueError("--refresh-stale requires production fetch")
        if args.mode == "production" and (args.source_ref or args.source_commit):
            raise ValueError("explicit source parameters require verification mode")
        verification = None
        if args.mode == "verification":
            if args.command == "address" or args.writer_owned:
                raise ValueError("verification requires publish/fetch with its own private cache guard")
            verification = verification_identity(args.repository, args.source_ref, args.source_commit, operation_deadline())
        partition = partition_path(args.repository)
        if args.command == "address":
            cache_key = release_key(args.repository)
            print(json.dumps({"partition": partition, "cache_key": cache_key,
                              "release_prefix": prefix(partition, cache_key), "asset": ASSET}))
            return 0
        if args.command == "fetch":
            if verification is not None:
                return fetch_verification(args.repository, partition, verification)
            return fetch(args.repository, partition, args.writer_owned, args.refresh_stale)
        return publish(args.repository, partition, verification)
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        receipt(args.command, "miss" if args.command == "fetch" else "failed",
                reason=("verification: " if args.mode == "verification" else "") + str(error))
        return 1 if args.command == "fetch" else 2


if __name__ == "__main__":
    raise SystemExit(main())
