"""Actions snapshots are optional, integrity-checked inputs to normal producers."""
from __future__ import annotations

import argparse
import errno
import hashlib
import json
import os
import pathlib
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import tarfile
import time

from lean_cache import binary_platform, partition_path, resolved_mathlib
from lean_cache_release import cache_guard
from cache_material import files, sha, snapshot_files, validate_manifest

LAYERS = ("dependency", "project")
# Execution evidence is opt-in; native engineering/current owners produce it.
EXECUTION_LAYERS = ("engineering", "current")
ALL_LAYERS = (*LAYERS, "judge", *EXECUTION_LAYERS, "elan")


def actions_keys(root: pathlib.Path) -> dict:
    """Build Actions snapshot keys and enforce the write policy.

    Actions transport identity belongs to this module; lean_cache.py only
    provides semantic inputs and platform partition helpers used by producers.
    """
    revision = resolved_mathlib(root)
    system, machine = binary_platform()
    run = os.environ.get("GITHUB_RUN_ID", "")
    attempt = os.environ.get("GITHUB_RUN_ATTEMPT", "")
    if not re.fullmatch(r"[0-9]+", run) or not re.fullmatch(r"[0-9]+", attempt):
        raise ValueError("snapshot keys require GITHUB_RUN_ID and GITHUB_RUN_ATTEMPT")
    writer_allowed = (os.environ.get("GITHUB_EVENT_NAME") == "push"
                  and (os.environ.get("GITHUB_REF") == "refs/heads/dev"
                       or os.environ.get("GITHUB_REF", "").startswith("refs/heads/integration-"))
                  and os.environ.get("STRATALINT_CACHE_WRITES", "true") == "true")
    result = {"mathlib_revision": revision, "os": system, "arch": machine,
              "partition": partition_path(root),
              "save_allowed": writer_allowed and os.environ.get("STRATALINT_CHECK_SUCCEEDED") == "true",
              # A compilation seed attests production, never engineering/current checks.
              "judge_save_allowed": writer_allowed and os.environ.get("STRATALINT_BUILD_SUCCEEDED") == "true"}
    paths = {"dependency": ".lake/packages", "project": ".lake/build",
             "judge": ".judge-binaries"}
    for layer, path in paths.items():
        prefix = f"lean-{layer}-v3-{revision}-{system}-{machine}-"
        result[layer] = {"restore_prefix": prefix, "key": f"{prefix}{run}-{attempt}",
                         "path": "build/lean-cache/" + layer, "target": path}
    for layer in EXECUTION_LAYERS:
        prefix = f"lean-{layer}-seed-v1-{revision}-{system}-{machine}-"
        result[layer] = {"restore_prefix": prefix, "key": f"{prefix}{run}-{attempt}",
                         "path": "build/lean-cache/" + layer, "stage": layer + "-seed"}
    result["release_prefix"] = f"lean-cache-v2-{revision}-{system}-{machine}-"
    return result


def output(values, destination="GITHUB_OUTPUT"):
    text = "".join(f"{key}={str(value).lower() if isinstance(value, bool) else value}\n" for key, value in values.items())
    if os.environ.get(destination):
        try:
            with open(os.environ[destination], "a", encoding="utf-8") as stream:
                stream.write(text)
        except OSError as error:
            receipt("all", "output-unavailable", reason=str(error))
    print(text, end="")


def receipt(layer, status, **fields):
    print("LEAN_ACTIONS_CACHE " + json.dumps({"layer": layer, "status": status, **fields}, sort_keys=True))


def accepted_current(root):
    """Consume the current producer's accepted handoff without rerunning it."""
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "lean-inspector"))
    from publication import SUFFIXES

    transport = json.loads((root / "build/ci/current-transport.json").read_text())
    if (not isinstance(transport, dict) or transport.get("version") != 1 or transport.get("stage") != "current"
            or transport.get("commit") != os.environ["CANDIDATE_SHA"]
            or transport.get("run_id") != int(os.environ["GITHUB_RUN_ID"])
            or transport.get("run_attempt") != int(os.environ["GITHUB_RUN_ATTEMPT"])
            or transport.get("repository") != os.environ["GITHUB_REPOSITORY"]
            or not re.fullmatch(r"[0-9a-f]{64}", transport.get("candidate", ""))
            or not isinstance(transport.get("round"), str) or not transport["round"].strip()):
        raise ValueError("current transport execution mismatch")
    transported = {item["path"]: item for item in transport["materials"]}
    if len(transported) != len(transport["materials"]):
        raise ValueError("duplicate current transport member")

    def bound_bytes(path):
        full = root / path
        data = full.read_bytes()
        if hashlib.sha256(data).hexdigest() != transported[path]["sha256"]:
            raise ValueError("current handoff integrity mismatch: " + path)
        return data

    summary = json.loads(bound_bytes("build/ci/current-result.json"))
    current = json.loads(bound_bytes("build/ci/current.json"))
    if (not isinstance(summary, dict) or summary.get("stage") != "current" or summary.get("exit") != 0
            or summary.get("current_evidence") != "build/ci/current.json"
            or not isinstance(current, dict) or current.get("version") != 2
            or current.get("candidate") != transport["candidate"] or current.get("round") != transport["round"]
            or summary.get("candidate") != current["candidate"]):
        raise ValueError("current report handoff mismatch")
    required_steps = ["lean-report", "scribe", "filemap", "check-current"]
    selection = current.get("selection")
    if selection is not None:
        sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "workflow"))
        from ci_plan import make_plan, same_record
        if not isinstance(selection, dict) or set(selection) != {"plan", "changes"}:
            raise ValueError("invalid current resource selection")
        for selected in selection.values():
            if pathlib.PurePosixPath(selected).is_absolute() or any(part in ("", ".", "..") for part in selected.split("/")):
                raise ValueError("invalid current selection material")
            bound_bytes(selected)
        plan = json.loads(bound_bytes(selection["plan"]))
        if not same_record(plan, make_plan(root, transport["commit"], root / selection["changes"])):
            raise ValueError("current selection differs from validated scope")
        required_steps = plan["execution"]["steps"]
    if ([step.get("name") for step in current["steps"]] != required_steps
            or any(step.get("raw_exit") != 0 or step.get("exit") != 0
                   or not (step.get("status") == "executed" or step.get("status") == "reused"
                           and step.get("name") in ("scribe", "filemap", "check-current")) for step in current["steps"])
            or summary.get("report") != (".lake/build/stratalint/raw-lean-report.json"
                if "lean-report" in required_steps else None)):
        raise ValueError("current requires complete selected obligations")
    clean_current_candidate(root, transport["commit"])
    accepted = {item["path"]: item["sha256"] for item in current["materials"]}
    if len(accepted) != len(current["materials"]):
        raise ValueError("duplicate current material")
    if "lean-report" not in required_steps:
        return transport, current, None, accepted
    relative = summary["report"]
    if pathlib.PurePosixPath(relative).is_absolute() or any(part in ("", ".", "..") for part in relative.split("/")):
        raise ValueError("invalid current report path")
    for suffix in SUFFIXES:
        path = relative + suffix
        full = root / path
        mode = 0 if os.name == "nt" else full.stat().st_mode & 0o7777
        if (full.is_symlink() or not full.is_file() or accepted[path] != transported[path]["sha256"]
                or mode != transported[path]["mode"] or sha(full) != accepted[path]):
            raise ValueError("current report member mismatch: " + path)
    report = root / relative
    if (report.with_name(report.name + ".sha256").read_text(encoding="ascii")
            != f"{accepted[relative]}  {report.name}\n"):
        raise ValueError("current report checksum mismatch")

    return transport, current, report, accepted


def clean_current_candidate(root, commit):
    for args, expected_output in ((["rev-parse", "HEAD"], commit),
                                  (["status", "--porcelain", "--untracked-files=all"], "")):
        result = subprocess.run(["git", "-C", str(root), *args], capture_output=True, text=True)
        if result.returncode or result.stdout.strip() != expected_output:
            raise ValueError("current snapshot requires the exact clean candidate commit")


def snapshot_execution(root, layer, keys, destination):
    """Export one native execution seed and make its declared members cacheable.

    The native runner owns seed selection, validation, provenance, and the
    NUL material list.  Actions only transports the resulting files.
    """
    spec = keys[layer]
    commit = os.environ.get("CANDIDATE_SHA", "")
    if commit and not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("CANDIDATE_SHA must be a 40-character commit identity")
    if not commit:
        result = subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD"], capture_output=True, text=True, check=True)
        commit = result.stdout.strip()
    runner = root / "tools/StrataLint.EngineeringScope/bin/Release/net10.0/StrataLint.EngineeringScope.dll"
    if not runner.is_file():
        raise ValueError("native execution transport runner is unavailable")
    destination.mkdir(parents=True, exist_ok=True)
    descriptor, archive_name = tempfile.mkstemp(prefix=f".{layer}-transport-", suffix=".tgz", dir=destination.parent)
    os.close(descriptor)
    archive = pathlib.Path(archive_name)
    command = ["dotnet", str(runner), "transport-pack", "--repository", str(root),
               "--stage", spec["stage"], "--commit", commit,
               "--run-id", os.environ["GITHUB_RUN_ID"],
               "--run-attempt", os.environ["GITHUB_RUN_ATTEMPT"], "--archive", str(archive)]
    try:
        try:
            subprocess.run(command, cwd=root, check=True, capture_output=True, text=True)
        except subprocess.CalledProcessError as error:
            status = subprocess.run(["git", "-C", str(root), "status", "--porcelain", "--untracked-files=all"], capture_output=True, text=True)
            detail = (error.stderr or error.stdout or str(error)).strip()
            raise ValueError(detail + ("; status=" + status.stdout.strip() if status.stdout.strip() else "")) from error
        with tarfile.open(archive, "r:gz") as source:
            for member in source.getmembers():
                path = pathlib.PurePosixPath(member.name)
                if (not member.isfile() or path.is_absolute() or any(part in ("", ".", "..") for part in member.name.split("/"))):
                    raise ValueError("native execution transport contains an invalid member")
                target = destination / path
                target.parent.mkdir(parents=True, exist_ok=True)
                with source.extractfile(member) as stream:
                    if stream is None:
                        raise ValueError("native execution transport member has no data")
                    target.write_bytes(stream.read())
                if os.name != "nt":
                    target.chmod(member.mode & 0o7777)
    finally:
        archive.unlink(missing_ok=True)
        archive.with_name(archive.name + ".tmp").unlink(missing_ok=True)
    inventory = files(destination)
    transport = json.loads((destination / "build/ci" / (spec["stage"] + "-transport.json")).read_text())
    if transport.get("commit") != commit or transport.get("run_id") != int(os.environ["GITHUB_RUN_ID"]):
        raise ValueError("native execution transport identity mismatch")
    if transport.get("run_attempt") != int(os.environ["GITHUB_RUN_ATTEMPT"]):
        raise ValueError("native execution transport attempt mismatch")
    return inventory


def restore_execution(root, layer, keys, staged):
    spec = keys[layer]
    transport_path = staged / "build/ci" / (spec["stage"] + "-transport.json")
    transport = json.loads(transport_path.read_text())
    if (not isinstance(transport, dict) or transport.get("stage") != spec["stage"]
            or not re.fullmatch(r"[0-9a-f]{40}", transport.get("commit", ""))):
        raise ValueError("invalid native execution transport identity")
    runner = root / "tools/StrataLint.EngineeringScope/bin/Release/net10.0/StrataLint.EngineeringScope.dll"
    if not runner.is_file():
        raise ValueError("native execution transport runner is unavailable")
    inventory = files(staged)
    # Native validation must inspect the complete staged bundle before any
    # optional seed material can replace destination evidence.
    try:
        subprocess.run(["dotnet", str(runner), "transport-verify", "--repository", str(staged),
                        "--stage", spec["stage"], "--commit", transport["commit"],
                        "--run-id", str(transport["run_id"]), "--run-attempt", str(transport["run_attempt"])],
                       cwd=root, check=True, capture_output=True, text=True)
    except subprocess.CalledProcessError as error:
        detail = (error.stderr or error.stdout or str(error)).strip()
        raise ValueError("native execution transport rejected staged seed: " + detail) from error
    # Native verification owns the accepted material list; the copying adapter
    # must not extend it with extra rows from the outer Actions inventory.
    declared = {item["path"] for item in transport["materials"]}
    if {item["path"] for item in inventory} != declared | {transport_path.relative_to(staged).as_posix()}:
        raise ValueError("execution seed differs from declared transport materials")
    with tempfile.TemporaryDirectory(prefix=".transport-rollback-", dir=root.parent) as rollback:
        rollback_root = pathlib.Path(rollback)
        backups = []
        installed = []
        try:
            for item in inventory:
                source = staged / item["path"]
                destination = root / item["path"]
                destination.parent.mkdir(parents=True, exist_ok=True)
                if destination.exists():
                    backup = rollback_root / item["path"]
                    backup.parent.mkdir(parents=True, exist_ok=True)
                    shutil.move(destination, backup)
                    backups.append((destination, backup))
                shutil.copy2(source, destination)
                installed.append(destination)
        except Exception:
            for destination in installed:
                destination.unlink(missing_ok=True)
            for destination, backup in reversed(backups):
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.move(backup, destination)
            raise


def validate_judge_registration(root, layers):
    if "judge" in layers:
        sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "report"))
        from dotnet_producer import project_registry
        return project_registry(root)


def validate_cache_directory(directory, expected, *, small_files_first=False):
    """Validate a complete cache data directory before publishing it.

    ``files(..., expected=...)`` validates the declared bytes and modes but
    intentionally ignores unlisted neighbours because its copy mode only
    materializes declared members.  A same-filesystem move would otherwise
    publish those neighbours, so inspect the regular-file shape separately
    while keeping the declared member hash pass to one read. Empty directories
    are permitted because snapshot manifests intentionally register files only.
    """
    if directory.is_symlink() or not directory.is_dir():
        raise ValueError("cache data is not a private directory")
    validate_manifest(expected)
    declared = {item["path"]: item["mode"] for item in expected}
    actual = {}
    for path in directory.rglob("*"):
        relative = path.relative_to(directory).as_posix()
        if path.is_symlink():
            raise ValueError("cache data contains a symlink: " + relative)
        if path.is_dir():
            continue
        if not path.is_file():
            raise ValueError("cache data member is not a regular file: " + relative)
        metadata = path.stat()
        if relative in declared and metadata.st_mode & 0o777 != declared[relative]:
            raise ValueError("cache material integrity mismatch: " + relative)
        actual[relative] = metadata.st_size
    if actual.keys() != declared.keys():
        extra = sorted(actual.keys() - declared.keys())
        missing = sorted(declared.keys() - actual.keys())
        detail = []
        if extra:
            detail.append("extra=" + ",".join(extra[:3]))
        if missing:
            detail.append("missing=" + ",".join(missing[:3]))
        raise ValueError("cache data members differ from manifest (" + ";".join(detail) + ")")
    if small_files_first:
        expected = sorted(expected, key=lambda item: (actual[item["path"]], item["path"]))
    return files(directory, expected=expected)


def move_validated_cache_data(cached, staged, expected):
    """Move a same-filesystem cache payload into private staging.

    The move removes the large second copy used by the old restore path.  The
    payload is validated after moving, so a byte race cannot publish unchecked
    data; a validation failure moves it back to the Actions cache directory.
    Cross-device filesystems retain the old copy-and-hash fallback.
    """
    try:
        cached.rename(staged)
    except OSError as error:
        if error.errno not in (errno.EXDEV, errno.EACCES, errno.EPERM):
            raise
        files(cached, expected=expected, copy_to=staged)
        return False
    try:
        validate_cache_directory(staged, expected)
    except BaseException:
        try:
            staged.rename(cached)
        except OSError as rollback_error:
            raise ValueError("cache validation failed and source rollback failed") from rollback_error
        raise
    return True


def replace_restored_directory(staged, target, rollback_root):
    """Atomically publish a validated directory while retaining old target."""
    previous = rollback_root / "previous"
    had_target = target.exists() or target.is_symlink()
    if had_target:
        rollback_root.mkdir(parents=True, exist_ok=True)
        target.rename(previous)
    try:
        staged.rename(target)
    except BaseException:
        if had_target and (previous.exists() or previous.is_symlink()):
            previous.rename(target)
        raise
    if had_target:
        if previous.is_dir() and not previous.is_symlink():
            shutil.rmtree(previous)
        else:
            previous.unlink()


def stage_snapshot(root, keys, layer, staged, registry=None, *, current=None):
    """Produce a private layer; only the parent may publish it and report ready."""
    spec = keys[layer]
    if current is not None and layer in ("dependency", "project"):
        if not current_built_lean(root, *current):
            metrics = {"save_disabled_reason": "current did not execute a successful Lean build"}
            (staged / "metrics.json").write_text(json.dumps(metrics) + "\n")
            return metrics
    with cache_guard(root, shared=True):
        if layer in ("dependency", "project") and unchanged_layer(root, keys[layer], layer, keys["partition"]):
            metrics = {"save_disabled_reason": "unchanged"}
            (staged / "metrics.json").write_text(json.dumps(metrics) + "\n")
            return metrics
        if layer in EXECUTION_LAYERS:
            inventory = snapshot_execution(root, layer, keys, staged / "data")
        elif layer == "judge":
            sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "report"))
            from dotnet_producer import stage_seed
            stage_seed(root, staged / "data", registry)
            inventory = files(staged / "data")
        else:
            inventory = snapshot_files(root / spec["target"], staged / "data",
                                       materialize_links=layer == "dependency")
    manifest = {"schema": "lean-actions-seed-v1", "partition": keys["partition"], "layer": layer,
                "key": spec["key"], "files": inventory}
    (staged / "manifest.json").write_text(json.dumps(manifest, sort_keys=True) + "\n")
    sizes = [(item, (staged / "data" / item["path"]).stat().st_size) for item in inventory]
    metrics = {"file_count": len(inventory), "uncompressed_bytes": sum(size for _, size in sizes),
               "largest_files": [{"path": item["path"], "sha256": item["sha256"], "size_bytes": size}
                                 for item, size in sorted(sizes, key=lambda pair: (-pair[1], pair[0]["path"]))[:5]]}
    (staged / "metrics.json").write_text(json.dumps(metrics, sort_keys=True) + "\n")
    return metrics


def unchanged_layer(root, spec, layer, partition):
    """Check whether a restored layer already contains the exact current material.

    Only a seed successfully restored in this execution may suppress a save.
    Check shape and modes first, then compare small files before large ones so
    changed provenance avoids hashing all large materials before a new snapshot.
    Every declared file must match; malformed, stale or rejected seeds fall
    through to a new snapshot.
    """
    manifest_path = root / spec["path"] / "manifest.json"
    restored_path = root / spec["path"] / "restored.json"
    try:
        if manifest_path.is_symlink() or restored_path.is_symlink():
            return False
        manifest_bytes = manifest_path.read_bytes()
        manifest = json.loads(manifest_bytes)
        restored = json.loads(restored_path.read_bytes())
        if (not isinstance(manifest, dict) or manifest.get("schema") != "lean-actions-seed-v1"
                or manifest.get("partition") != partition
                or manifest.get("layer") != layer
                or restored != {"schema": "lean-actions-restored-v1", "snapshot_key": spec["key"],
                                "manifest_sha256": hashlib.sha256(manifest_bytes).hexdigest()}):
            return False
        target = root / spec["target"]
        validate_cache_directory(target, manifest.get("files"), small_files_first=True)
        return True
    except (OSError, ValueError, TypeError, KeyError, json.JSONDecodeError):
        return False


def current_built_lean(root, plan, commit):
    """Bind heavy current snapshots to accepted work from this execution."""
    step = "lean-report" if "lean-report" in plan["execution"]["steps"] else "lean"
    if step not in plan["execution"]["steps"]:
        return False
    transport, current, report, _ = accepted_current(root)
    if transport["commit"] != commit:
        raise ValueError("current Lean build belongs to another candidate")
    # Native report execution always requires the default Lean targets and
    # inspector build. An executed, accepted report therefore attests both.
    if step == "lean-report" and report is None:
        raise ValueError("current Lean build has no accepted native report")
    return any(item["name"] == step and item["status"] == "executed" and item["raw_exit"] == 0
        and item["exit"] == 0 for item in current["steps"])


def bounded_snapshot(root, layer, staged, seconds, *, current=False):
    command = [sys.executable, str(pathlib.Path(__file__).resolve()), "snapshot", "--repository", str(root),
               *(["--stage", "current", "--layer", layer] if current else ["--layers", layer]),
               "--snapshot-directory", str(staged)]
    env = dict(os.environ)
    env.pop("GITHUB_OUTPUT", None)
    handlers = {signum: signal.getsignal(signum) for signum in (signal.SIGTERM, signal.SIGINT)}

    def cancelled(signum, _frame):
        raise SystemExit(128 + signum)

    process = None
    with tempfile.TemporaryFile() as log:
        try:
            for signum in handlers:
                signal.signal(signum, cancelled)
            process = subprocess.Popen(command, env=env, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
            try:
                result = process.wait(timeout=seconds)
            except subprocess.TimeoutExpired as error:
                raise ValueError("snapshot exceeded remaining cache window") from error
            if result:
                log.seek(0)
                raise ValueError("snapshot worker failed: " + log.read(4096).decode(errors="replace"))
        finally:
            try:
                if process is not None:
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    if process.poll() is None:
                        process.wait(timeout=5)
            finally:
                for signum, handler in handlers.items():
                    signal.signal(signum, handler)


def snapshot(root, keys, layers=LAYERS, registry=None, *, deadline=None, current=None):
    registry = registry if registry is not None else validate_judge_registration(root, layers)
    for layer in layers:
        ready, committed, save_minutes = False, False, 1
        try:
            if not keys["judge_save_allowed" if layer == "judge" else "save_allowed"]:
                receipt(layer, "save-disabled")
                continue
            seconds = deadline.snapshot_seconds() if deadline is not None else None
            if seconds is not None and seconds <= 0:
                receipt(layer, "save-disabled", reason=deadline.reason)
                continue
            started = time.monotonic()
            spec = keys[layer]
            target = root / spec["path"]
            target.parent.mkdir(parents=True, exist_ok=True)
            with tempfile.TemporaryDirectory(prefix=".snapshot-", dir=target.parent) as temporary:
                staged = pathlib.Path(temporary)
                if deadline is None:
                    metrics = stage_snapshot(root, keys, layer, staged, registry, current=current)
                else:
                    bounded_snapshot(root, layer, staged, seconds, current=current is not None)
                    save_minutes = deadline.save_timeout_minutes()
                    if not save_minutes:
                        raise ValueError("snapshot left no cache save window")
                    metrics = json.loads((staged / "metrics.json").read_text())
                if "save_disabled_reason" in metrics:
                    receipt(layer, "save-disabled", reason=metrics["save_disabled_reason"])
                    continue
                with cache_guard(root), tempfile.TemporaryDirectory(prefix=".snapshot-backup-", dir=target.parent) as backup:
                    previous = pathlib.Path(backup) / "previous"
                    if target.exists():
                        target.rename(previous)
                    try:
                        staged.rename(target)
                    except BaseException:
                        if previous.exists():
                            previous.rename(target)
                        raise
                    committed = True
                # The job window reserves cleanup time. Filesystem cleanup is
                # not a hard deadline: late completion disables the remote save.
                if deadline is not None:
                    save_minutes = deadline.save_timeout_minutes()
                    if not save_minutes:
                        raise ValueError("snapshot publication left no cache save window")
                ready = True
                receipt(layer, "snapshot", key=spec["key"], elapsed_seconds=round(time.monotonic() - started, 3), **metrics)
        except (OSError, ValueError, TypeError, KeyError, subprocess.SubprocessError) as error:
            receipt(layer, "save-disabled" if committed else "save-failed", reason=str(error))
        finally:
            values = {layer + "_ready": ready}
            if deadline is not None:
                values["save_timeout_minutes"] = save_minutes if ready else 1
            output(values)


def stamp_restored_dependency(root, keys):
    """Publish the LeanCacheStamp contract after verified dependency installation.

    This records partition identity only, just like the C# producer's stamp.
    It does not attest cache completeness or a successful build/report.
    The restore caller owns the shared cache writer guard through publication.
    """
    lake = root / ".lake"
    descriptor, name = tempfile.mkstemp(prefix=".stratalint-lean-cache-stamp.", suffix=".tmp", dir=lake)
    temporary = pathlib.Path(name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            json.dump({"schema": "stratalint-lean-cache-v2", "mathlib_revision": keys["mathlib_revision"],
                       "os": keys["os"], "arch": keys["arch"]}, stream)
            stream.write("\n")
        temporary.replace(lake / ".stratalint-lean-cache-stamp.json")
    finally:
        temporary.unlink(missing_ok=True)


def restore(root, keys, matched, layers=LAYERS, registry=None):
    if registry is None:
        validate_judge_registration(root, layers)
    project_seeded = False
    for layer in layers:
        try:
            spec = keys[layer]
            cached = root / spec["path"]
            restored_path = cached / "restored.json"
            restored_path.unlink(missing_ok=True)
            key = matched[layer]
            if not key:
                receipt(layer, "miss", reason="Actions supplied no cache")
                continue
            if not re.fullmatch(re.escape(spec["restore_prefix"]) + r"[0-9]+-[0-9]+", key):
                raise ValueError("Actions seed is outside the selected partition")
            manifest_bytes = (cached / "manifest.json").read_bytes()
            manifest = json.loads(manifest_bytes)
            if (not isinstance(manifest, dict) or manifest.get("schema") != "lean-actions-seed-v1" or manifest.get("partition") != keys["partition"]
                    or manifest.get("layer") != layer or manifest.get("key") != key):
                raise ValueError("Actions seed identity or material integrity mismatch")
            stream_copy = layer in ("dependency", "project")
            if not stream_copy:
                inventory = files(cached / "data", expected=manifest.get("files"))
            target = root / spec.get("target", ".")
            with cache_guard(root):
                target.parent.mkdir(parents=True, exist_ok=True)
                with tempfile.TemporaryDirectory(prefix=".actions-", dir=target.parent) as temporary:
                    staged = pathlib.Path(temporary) / "data"
                    direct = False
                    if stream_copy:
                        # Actions puts a manifest beside ``data``.  Consume the
                        # data directory by rename on the normal same-device
                        # runner; this avoids a second 25 GB copy before Lake.
                        direct = move_validated_cache_data(cached / "data", staged, manifest.get("files"))
                    else:
                        # Execution seeds must remain independently validated
                        # material because their native verifier consumes the
                        # complete staged bundle.
                        staged.mkdir()
                        inventory = files(cached / "data", expected=manifest.get("files"))
                        for item in inventory:
                            destination = staged / item["path"]
                            destination.parent.mkdir(parents=True, exist_ok=True)
                            shutil.copy2(cached / "data" / item["path"], destination)
                    if layer in EXECUTION_LAYERS:
                        restore_execution(root, layer, keys, staged)
                    else:
                        try:
                            replace_restored_directory(staged, target, pathlib.Path(temporary) / "rollback")
                        except BaseException:
                            # A failed publication must not consume a valid
                            # same-filesystem Actions payload.
                            if direct and staged.exists() and not (cached / "data").exists():
                                staged.rename(cached / "data")
                            raise
                if layer == "dependency":
                    stamp_restored_dependency(root, keys)
                if stream_copy:
                    restored_path.write_text(json.dumps({"schema": "lean-actions-restored-v1",
                        "snapshot_key": spec["key"],
                        "manifest_sha256": hashlib.sha256(manifest_bytes).hexdigest()}) + "\n")
            project_seeded |= layer == "project"
            receipt(layer, "restored", key=key, partition=keys["partition"])
        except (OSError, ValueError, TypeError, KeyError, subprocess.CalledProcessError) as error:
            receipt(layer, "miss", reason=str(error))
    # A dependency-only hit cannot suppress the project Release fallback.
    if "project" in layers:
        output({"STRATALINT_ACTIONS_CACHE_SEEDED": "1" if project_seeded else "0"}, "GITHUB_ENV")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("keys", "restore", "snapshot"))
    parser.add_argument("--repository", required=True, type=pathlib.Path)
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--layers", choices=ALL_LAYERS, nargs="+", default=LAYERS)
    selection.add_argument("--stage", choices=("build", "engineering", "current", "delta"))
    parser.add_argument("--layer", choices=ALL_LAYERS)
    parser.add_argument("--bounded-cache", action="store_true")
    parser.add_argument("--snapshot-directory", type=pathlib.Path, help=argparse.SUPPRESS)
    for layer in ALL_LAYERS:
        parser.add_argument("--" + layer + "-key", default="")
    args = parser.parse_args()
    if args.layer and not args.stage:
        parser.error("--layer requires --stage")
    if args.bounded_cache and (args.command != "snapshot" or not args.layer or args.stage not in ("build", "engineering", "current")):
        parser.error("--bounded-cache requires snapshot with --stage and --layer")
    if args.snapshot_directory and (args.command != "snapshot" or args.bounded_cache
            or not (args.stage == "current" and args.layer or not args.stage and len(args.layers) == 1)):
        parser.error("snapshot worker requires exactly one explicit layer")
    if args.stage:
        # Routing is required input validation, outside optional-cache failure handling.
        sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "workflow"))
        import ci_plan
        try:
            root = args.repository.resolve()
            commit = ci_plan.git(root, "rev-parse", "HEAD").decode().strip()
            if os.environ.get("CANDIDATE_SHA", commit) != commit:
                raise ValueError("cache checkout does not match fixed candidate")
            plan = ci_plan.validate_plan(root, commit,
                root / os.environ["CI_PLAN_PATH"], root / os.environ["CI_CHANGES_PATH"])
            requirements = ci_plan.stage_requirements(root, plan, args.stage)
            args.layers = requirements["cache_layers"]
        except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
            print("CI_INPUT_FAILED " + str(error), file=sys.stderr)
            return 2
        if args.layer:
            args.layers = [args.layer] if args.layer in args.layers else []
            if not args.layers:
                receipt(args.layer, "save-disabled", reason="layer not required by registered stage")
                values = {args.layer + "_ready": False}
                if args.bounded_cache:
                    values["save_timeout_minutes"] = 1
                output(values)
        if not args.layers:
            return 0
    current = (plan, commit) if args.command == "snapshot" and args.stage == "current" else None
    elan = "elan" in args.layers or args.stage is None
    args.layers = [layer for layer in args.layers if layer != "elan"]
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "report"))
    from dotnet_producer import ProjectRegistrationError
    try:
        registry = validate_judge_registration(args.repository, args.layers) if args.command != "keys" else None
        keys = actions_keys(args.repository)
        if args.snapshot_directory:
            stage_snapshot(args.repository, keys, args.layers[0], args.snapshot_directory, registry, current=current)
        elif args.command == "keys":
            values = {}
            values.update({key: keys[key] for key in
                           ("mathlib_revision", "os", "arch", "partition", "save_allowed", "judge_save_allowed", "release_prefix")})
            for layer in args.layers:
                values.update({layer + "_" + key: value for key, value in keys[layer].items()})
            if elan:
                system, arch = binary_platform()
                toolchain = hashlib.sha256((args.repository / "lean-toolchain").read_bytes()).hexdigest()
                values["elan_key"] = f"elan-v1-{system}-{arch}-{toolchain}"
            output(values)
        elif args.command == "restore":
            restore(args.repository, keys, {layer: getattr(args, layer + "_key") for layer in args.layers}, args.layers, registry)
        else:
            deadline = None
            if args.bounded_cache:
                from cache_deadline import load_deadline
                deadline = load_deadline(args.repository, args.stage)
            snapshot(args.repository, keys, args.layers, registry, deadline=deadline, current=current)
        return 0
    except ProjectRegistrationError as error:
        print(str(error), file=sys.stderr)
        return 2
    except (OSError, ValueError, TypeError, KeyError, subprocess.CalledProcessError) as error:
        receipt("all", "unavailable", reason=str(error))
        if args.snapshot_directory:
            return 1
        if args.bounded_cache:
            output({args.layer + "_ready": False, "save_timeout_minutes": 1})
        if args.command == "restore" and "project" in args.layers:
            output({"STRATALINT_ACTIONS_CACHE_SEEDED": "0"}, "GITHUB_ENV")
        return 0


if __name__ == "__main__":
    raise SystemExit(main())
