"""Optional, immutable Release snapshots; never a check verdict or a source selector."""
from __future__ import annotations

import argparse
import base64
import contextlib
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

from lean_cache import manifest_mathlib, normalized_platform, partition_path
from cache_material import sha

ASSET = "lean-build.tgz"
MANIFEST = "manifest.json"
LEGACY_MANIFEST = "manifest.txt"
REPO = os.environ.get("STRATALINT_CACHE_REPO", "the-omega-institute/trureturing")
# Issue #6194, run 34119746844: Release assets must be strictly below 2 GiB.
# Keep dev's 1.5 GiB headroom and two-digit, at-most-100-part inventory.
CHUNK_BYTES = 1610612736
# Optional transport policy (#5985, 2026-09-08): a ten-minute operation ceiling,
# configurable downward, leaves headroom over the recorded 5m08s Release fetch
# (#2634). This is a policy choice, not a throughput derivation or a copy of the
# C# ArchiveBudget. Review against real multipart transfers during integration.
# Fetch includes all snapshot attempts; publish starts only after the current report succeeds.
RELEASE_OPERATION_TIMEOUT_SECONDS = 600


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


def prefix(partition, verification=False):
    namespace = "lean-cache-verify-v1-" if verification else "lean-cache-v2-"
    return namespace + partition.replace("/", "-") + "-"


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
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "workflow"))
    from source_reference import validate_source_ref
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
            and item.get("tagName", "").startswith(prefix(partition))),
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
    # Build failures keep their status. Production transport is optional;
    # explicit verification succeeds only after the uploaded bytes restore.
    # A caller's LEAN_REPORT override must not move publication outside buildDir.
    build = subprocess.run(["make", "lean-report",
        "LEAN_REPORT=.lake/build/stratalint/raw-lean-report.json"], cwd=root)
    if build.returncode:
        return build.returncode
    report = root / ".lake/build/stratalint/raw-lean-report.json"
    if report.is_symlink() or not report.is_file():
        receipt("publish", "failed", reason="current Inspector report is missing")
        return 1 if verification is not None else 0
    try:
        payload = json.loads(report.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        receipt("publish", "failed", reason="current Inspector report is unreadable: " + str(error))
        return 1 if verification is not None else 0
    if (not isinstance(payload, dict) or payload.get("schema") != "stratalint-raw-lean-report-v2"
            or not isinstance(payload.get("modules"), list)):
        receipt("publish", "failed", reason="current Inspector report is malformed")
        return 1 if verification is not None else 0
    if verification is None and (os.environ.get("GITHUB_EVENT_NAME") != "schedule"
                                 or os.environ.get("GITHUB_REF") != "refs/heads/dev"):
        receipt("publish", "skipped", reason="Release publication requires the scheduled dev producer")
        return 0
    try:
        deadline = operation_deadline()
        commit = os.environ.get("GITHUB_SHA", "")
        run = os.environ.get("GITHUB_RUN_ID", "")
        attempt = os.environ.get("GITHUB_RUN_ATTEMPT", "")
        if not re.fullmatch(r"[0-9a-f]{40}", commit) or not all(
                re.fullmatch(r"[0-9]+", value) for value in (run, attempt)):
            raise ValueError("snapshot publication requires commit, run ID and attempt attribution")
        tag = prefix(partition, verification is not None) + run + "-" + attempt
        identity = {"producer_commit_sha": commit, "workflow_run_id": run, "workflow_run_attempt": attempt}
        existing = existing_release(tag, deadline)
        if existing is not None:
            if existing["draft"]:
                raise ValueError(f"exact release {tag} is an incomplete draft; refusing to modify it")
            if verification is not None:
                raise ValueError(f"verification release {tag} already exists; refusing to replace it")
            with tempfile.TemporaryDirectory(prefix="lean-release-confirm-") as temporary:
                snapshot_manifest(partition, tag, pathlib.Path(temporary), deadline,
                                  expected=identity, metadata=existing)
            receipt("publish", "exists", tag=tag, release_target=existing.get("target_commitish"), **identity)
            return 0
        with tempfile.TemporaryDirectory(prefix="lean-release-") as temporary:
            stage = pathlib.Path(temporary)
            with cache_guard(root, shared=True):
                if (root / ".lake").is_symlink() or not (root / ".lake/build").is_dir():
                    raise ValueError("no private project build to publish")
                # This archive is a replaceable seed: level 1 keeps the existing
                # gzip protocol without spending the transport window on level 9.
                with (stage / ASSET).open("wb") as output:
                    with tarfile.open(stage / ASSET, "w:gz", compresslevel=1,
                                      fileobj=ArchiveOutput(output, deadline)) as archive:
                        archive.add(root / ".lake/build", arcname="build")
            metadata = {"schema": "lean-release-seed-v3", "partition": partition,
                "producer_commit_sha": commit, "workflow_run_id": run, "workflow_run_attempt": attempt,
                "archive_sha256": archive_sha(stage / ASSET, deadline), "archive_bytes": (stage / ASSET).stat().st_size,
                "parts": archive_parts(stage, deadline)}
            if verification is not None:
                metadata.update(verification)
            (stage / MANIFEST).write_text(json.dumps(metadata, sort_keys=True) + "\n")
            # Never clobber an existing snapshot. Failed/racing publishers leave
            # at most a draft, which fetch never considers an applicable seed.
            # The server's default branch anchors only the storage container.
            # Actual producer identity stays in the transferred manifest.
            gh(deadline, "release", "create", tag, "--repo", REPO, "--draft",
               "--title", "Lean cache " + partition, "--notes", "Successful current Lean build and Inspector report; incremental seed only.")
            gh(deadline, "release", "upload", tag, *(str(stage / part["name"]) for part in metadata["parts"]),
               str(stage / MANIFEST), "--repo", REPO)
            gh(deadline, "release", "edit", tag, "--repo", REPO, "--draft=false")
            if verification is not None:
                # Prove this exact uploaded inventory through the normal restore
                # path into an empty private target before reporting publication.
                target, downloaded = stage / "verified-target", stage / "downloaded"
                target.mkdir()
                downloaded.mkdir()
                restore_snapshot(target, partition, tag, downloaded, deadline, metadata)
                pruned, prune_error = 0, None
            else:
                current = existing_release(tag, deadline)
                if current is None or current["draft"]:
                    raise ValueError(f"new snapshot {tag} is not readable as published; pruned nothing")
                confirmed = stage / "confirmed"
                confirmed.mkdir()
                snapshot_manifest(partition, tag, confirmed, deadline, expected=metadata, metadata=current)
                pruned, prune_error = prune(partition, tag, deadline)
            receipt("publish", "published", tag=tag, pruned=pruned, prune_error=prune_error, **metadata)
    except ImportError as error:
        receipt("publish", "skipped", reason="POSIX cache locking unavailable: " + str(error))
        return 1 if verification is not None else 0
    except (OSError, EOFError, ValueError, subprocess.SubprocessError, tarfile.TarError) as error:
        receipt("publish", "failed", reason=str(error))
        return 1 if verification is not None else 0
    return 0


def legacy_tag(tag):
    return re.fullmatch(r"lean-cache-v1-[A-Za-z0-9._-]+-[0-9a-f]{16}-[0-9a-f]{16}", tag) is not None


def legacy_manifest(path, metadata, partition, tag, deadline):
    """Adapt attributed cache data; never execute or use its source as a judge baseline."""
    fields = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        key, separator, value = line.partition("=")
        if not separator or not key or key in fields:
            raise ValueError("invalid legacy manifest field")
        fields[key] = value
    # Legacy address fields bind the transferred manifest to its published tag.
    # They never select compatibility: only resolved mathlib and platform do.
    hashes = [fields.get(key, "") for key in ("config_sha256", "sources_sha256")]
    if "build_snapshot_sha256" in fields:
        hashes.append(fields["build_snapshot_sha256"])
    if any(not re.fullmatch(r"[0-9a-f]{64}", value) for value in hashes):
        raise ValueError("invalid legacy snapshot address")
    toolchain = fields.get("toolchain", "")
    slug = re.sub(r"[^A-Za-z0-9]", "-", toolchain)
    expected_tag = "lean-cache-v1-" + slug + "-" + "-".join(value[:16] for value in hashes)
    if not toolchain or tag != expected_tag:
        raise ValueError("legacy snapshot addresses do not match release tag")
    commit, run = fields.get("producer_commit_sha", ""), fields.get("workflow_run_id", "")
    if (fields.get("tag") != tag or not re.fullmatch(r"[0-9a-f]{40}", commit)
            or not re.fullmatch(r"[1-9][0-9]*", run) or metadata.get("target_commitish") != commit
            or not isinstance(metadata.get("published_at"), str) or not metadata["published_at"]
            or fields.get("asset") != ASSET):
        raise ValueError("legacy snapshot source attribution mismatch")
    system, machine = normalized_platform(fields.get("os", ""), fields.get("arch", ""))
    if partition.split("/", 1)[1] != system + "-" + machine:
        raise ValueError("legacy snapshot platform mismatch")
    count = fields.get("parts", "1")
    if not re.fullmatch(r"[1-9][0-9]*", count) or not 1 <= int(count) <= 100:
        raise ValueError("invalid legacy archive parts inventory")
    count = int(count)
    assets = {asset["name"]: asset for asset in metadata["assets"]}
    manifest = {"producer_commit_sha": commit, "workflow_run_id": run,
        "archive_sha256": fields.get("archive_sha256", ""), "archive_bytes": int(fields.get("archive_bytes", "0")),
        "parts": [{"name": ASSET if count == 1 else f"{ASSET}.part-{index:02d}",
            "sha256": fields.get("archive_sha256" if count == 1 else f"part_sha256_{index}", ""),
            "bytes": assets.get(ASSET if count == 1 else f"{ASSET}.part-{index:02d}", {}).get("size")}
            for index in range(count)]}
    # Historical unchunked assets used GitHub's strict <2 GiB limit (e.g.
    # Release 383820945: 2,114,121,660 bytes); new/multipart writes keep 1.5 GiB.
    declared_parts(manifest, 2147483647 if count == 1 else CHUNK_BYTES)
    # Only legacy lacks a resolved mathlib field. These two requests establish
    # cache provenance, not candidate/base semantics or another cache selector.
    record = json.loads(gh(deadline, "api", f"repos/{REPO}/actions/runs/{run}"))
    if (not isinstance(record, dict) or type(record.get("id")) is not int or record["id"] != int(run)
            or record.get("event") != "schedule" or record.get("head_branch") != "dev"
            or record.get("head_sha") != commit or record.get("path") != ".github/workflows/lean-cache-publish.yml"
            or record.get("status") != "completed" or record.get("conclusion") != "success"
            or not isinstance(record.get("repository"), dict) or record["repository"].get("full_name") != REPO):
        raise ValueError("legacy snapshot has no matching successful scheduled dev producer")
    source = json.loads(gh(deadline, "api", f"repos/{REPO}/contents/lake-manifest.json?ref={commit}"))
    if (not isinstance(source, dict) or source.get("type") != "file" or source.get("path") != "lake-manifest.json"
            or source.get("encoding") != "base64" or not isinstance(source.get("content"), str)):
        raise ValueError("legacy producer lake-manifest is unavailable")
    content = base64.b64decode("".join(source["content"].split()), validate=True)
    blob = hashlib.sha1(b"blob " + str(len(content)).encode() + b"\0" + content).hexdigest()
    if source.get("sha") != blob or type(source.get("size")) is not int or source["size"] != len(content):
        raise ValueError("legacy producer lake-manifest blob mismatch")
    if manifest_mathlib(json.loads(content)) + "/" + system + "-" + machine != partition:
        raise ValueError("legacy snapshot mathlib partition mismatch")
    # Legacy recorded the run but not its producing attempt. Do not invent one
    # from the API's latest rerun, and do not emit a synthetic v3 publication.
    return manifest


def snapshot_manifest(partition, tag, stage, deadline, expected=None, verification=False, metadata=None):
    """Validate the small manifest and inventory before confirming or restoring a snapshot."""
    if metadata is None:
        metadata = json.loads(gh(deadline, "api", f"repos/{REPO}/releases/tags/{tag}"))
    if not isinstance(metadata, dict) or metadata.get("draft") is not False or metadata.get("tag_name") != tag:
        raise ValueError("snapshot is not published")
    legacy = not verification and legacy_tag(tag)
    manifest_name = LEGACY_MANIFEST if legacy else MANIFEST
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
    manifest = (legacy_manifest(stage / manifest_name, metadata, partition, tag, deadline) if legacy
                else json.loads((stage / manifest_name).read_text()))
    if not isinstance(manifest, dict):
        raise ValueError("snapshot manifest must be an object")
    commit, run, attempt = (manifest.get(field, "") for field in
        ("producer_commit_sha", "workflow_run_id", "workflow_run_attempt"))
    if not legacy and (manifest.get("schema") != "lean-release-seed-v3" or manifest.get("partition") != partition
            or not isinstance(commit, str) or not re.fullmatch(r"[0-9a-f]{40}", commit)
            or not all(isinstance(value, str) and re.fullmatch(r"[0-9]+", value) for value in (run, attempt))
            or tag != prefix(partition, verification) + run + "-" + attempt):
        raise ValueError("snapshot partition or source attribution mismatch")
    if expected is not None and any(manifest.get(key) != value for key, value in expected.items()):
        raise ValueError("snapshot does not match this exact publication")
    parts = manifest["parts"] if legacy else declared_parts(manifest)
    if sorted(recorded) != sorted([manifest_name, *[part["name"] for part in parts]]):
        raise ValueError("snapshot asset set is incomplete")
    if not legacy:
        assets_by_name = {asset["name"]: asset for asset in assets}
        for part in parts:
            asset = assets_by_name[part["name"]]
            if asset.get("digest") != "sha256:" + part["sha256"]:
                raise ValueError("transferred asset digest mismatch")
            if type(asset.get("size")) is not int or asset["size"] != part["bytes"]:
                raise ValueError("transferred asset size mismatch")
    return metadata, manifest, parts, legacy


def restore_snapshot(root, partition, tag, stage, deadline, verification=None):
    metadata, manifest, parts, legacy = snapshot_manifest(partition, tag, stage, deadline,
        expected=verification, verification=verification is not None)
    assets = metadata["assets"]
    commit, run = manifest["producer_commit_sha"], manifest["workflow_run_id"]
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
            if (path.is_absolute() or ".." in path.parts or (not path.parts and not (legacy and member.isdir()))
                    or (not legacy and path.parts[0] != "build")
                    or not (member.isfile() or member.isdir())):
                raise ValueError("archive contains an invalid cache member")
            if legacy:
                path = pathlib.PurePosixPath("build") / path
                member.name = str(path)
                member.pax_headers.pop("path", None)
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
                if target.exists() and (not target.is_dir() or any(target.iterdir())):
                    continue
                if target.is_dir():
                    target.rmdir()
                source.rename(target)
                installed.append(name)
    receipt("fetch", "unpacked" if installed else "skipped",
            mode="verification" if verification is not None else "partition", resolved=tag,
            installed=installed,
            producer_commit_sha=commit, workflow_run_id=run, partition=partition,
            release_target=metadata.get("target_commitish"))


def fetch_verification(root, partition, identity):
    tag = prefix(partition, True) + identity["workflow_run_id"] + "-" + identity["workflow_run_attempt"]
    try:
        deadline = operation_deadline()
        with cache_guard(root), tempfile.TemporaryDirectory(prefix="lean-fetch-verify-") as temporary:
            restore_snapshot(root, partition, tag, pathlib.Path(temporary), deadline, identity)
        return 0
    except (OSError, EOFError, ImportError, ValueError, KeyError, TypeError, subprocess.SubprocessError, tarfile.TarError) as error:
        receipt("fetch", "miss", mode="verification", reason=str(error), resolved=tag, partition=partition)
        return 1


def fetch(root, partition, writer_owned=False):
    if os.environ.get("STRATALINT_ACTIONS_CACHE_SEEDED", "").lower() in ("1", "true"):
        receipt("fetch", "skipped", reason="Actions supplied an applicable seed")
        return 0
    try:
        deadline = operation_deadline()
        with contextlib.nullcontext() if writer_owned else cache_guard(root):
            return fetch_locked(root, partition, deadline)
    except (OSError, ImportError, ValueError) as error:
        receipt("fetch", "miss", reason=str(error), partition=partition)
        return 1


def fetch_locked(root, partition, deadline):
    reason = "no published snapshot in this partition"
    try:
        releases = json.loads(gh(deadline, "release", "list", "--repo", REPO, "--limit", "100",
            "--json", "tagName,createdAt,isDraft"))
        for release in sorted(releases, key=lambda item: item["createdAt"], reverse=True):
            tag = release.get("tagName", "")
            if release.get("isDraft") is not False or not (tag.startswith(prefix(partition)) or legacy_tag(tag)):
                continue
            remaining(deadline)
            try:
                with tempfile.TemporaryDirectory(prefix="lean-fetch-") as temporary:
                    restore_snapshot(root, partition, tag, pathlib.Path(temporary), deadline)
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
    # Transition for the default dev ci.yml fetch caller; selection stays partitioned.
    # Remove after ci-push/ci-pr success and required-set migration, with its caller.
    parser.add_argument("--allow-seed", action="store_true", help=argparse.SUPPRESS)
    # Internal handoff from LeanArchiveFetch after its typed guard assertion.
    parser.add_argument("--writer-owned", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    try:
        if args.mode == "production" and (args.source_ref or args.source_commit):
            raise ValueError("explicit source parameters require verification mode")
        verification = None
        if args.mode == "verification":
            if args.command == "address" or args.writer_owned:
                raise ValueError("verification requires publish/fetch with its own private cache guard")
            verification = verification_identity(args.repository, args.source_ref, args.source_commit, operation_deadline())
        partition = partition_path(args.repository)
        if args.command == "address":
            print(json.dumps({"partition": partition, "release_prefix": prefix(partition), "asset": ASSET}))
            return 0
        if args.command == "fetch":
            if verification is not None:
                return fetch_verification(args.repository, partition, verification)
            return fetch(args.repository, partition, args.writer_owned)
        return publish(args.repository, partition, verification)
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        receipt(args.command, "miss" if args.command == "fetch" else "failed",
                reason=("verification: " if args.mode == "verification" else "") + str(error))
        return 1 if args.command == "fetch" else 2


if __name__ == "__main__":
    raise SystemExit(main())
