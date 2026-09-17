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
import stat
import subprocess
import sys
import tempfile
import tarfile
import time

from lean_cache import binary_platform, partition_path, resolved_mathlib
from lean_cache_release import cache_guard
from cache_material import CacheMaterialDifference, files, sha, snapshot_files, validate_manifest

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
    event, ref = os.environ.get("GITHUB_EVENT_NAME"), os.environ.get("GITHUB_REF", "")
    push_writer = event == "push" and (ref == "refs/heads/dev" or ref.startswith("refs/heads/integration-"))
    writer_allowed = push_writer and os.environ.get("STRATALINT_CACHE_WRITES") == "true"
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
    print("LEAN_ACTIONS_CACHE " + json.dumps({"layer": layer, "status": status, **fields}, sort_keys=True), flush=True)


def snapshot_phase(observations, name, boundary, started=None, *, sizes=None):
    """Best-effort snapshot costs; never used for reuse, budgets or verdicts."""
    if observations is None:
        return None
    try:
        if boundary == "start":
            observations[name] = {"status": "entered-without-completion"}
            return time.monotonic_ns()
        now = time.monotonic_ns()
        fields = {"status": "unavailable"}
        if started is not None and now >= started:
            fields = {"status": "completed", "elapsed_seconds": round((now - started) / 1_000_000_000, 6)}
        if sizes is not None:
            fields.update(file_count=len(sizes), material_bytes=sum(sizes.values()))
        observations[name] = fields
    except Exception:
        pass
    return None


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


def validate_cache_directory(directory, expected, *, small_files_first=False, observations=None,
                             private_staging=False):
    """Validate a complete cache data directory before publishing it.

    ``files(..., expected=...)`` validates the declared bytes and modes but
    intentionally ignores unlisted neighbours because its copy mode only
    materializes declared members.  A same-filesystem move would otherwise
    publish those neighbours, so inspect the regular-file shape separately
    while keeping the declared member hash pass to one read. Empty directories
    are permitted because snapshot manifests intentionally register files only.
    """
    shape_started = snapshot_phase(observations, "directory_shape", "start")
    if directory.is_symlink() or not directory.is_dir():
        raise CacheMaterialDifference("cache data is not a private directory", "invalid-layer-directory")
    validate_manifest(expected)
    declared = {item["path"]: item["mode"] for item in expected}
    actual = {}
    for path in directory.rglob("*"):
        relative = path.relative_to(directory).as_posix()
        metadata = path.lstat()
        if stat.S_ISLNK(metadata.st_mode):
            raise CacheMaterialDifference("cache data contains a symlink: " + relative, "symlink-member", relative)
        if stat.S_ISDIR(metadata.st_mode):
            continue
        if not stat.S_ISREG(metadata.st_mode):
            raise CacheMaterialDifference("cache data member is not a regular file: " + relative,
                                          "nonregular-member", relative)
        if relative in declared and metadata.st_mode & 0o777 != declared[relative]:
            raise CacheMaterialDifference("cache material integrity mismatch: " + relative, "mode-changed", relative)
        actual[relative] = metadata.st_size
    if actual.keys() != declared.keys():
        extra = sorted(actual.keys() - declared.keys())
        missing = sorted(declared.keys() - actual.keys())
        detail = []
        if extra:
            detail.append("extra=" + ",".join(extra[:3]))
        if missing:
            detail.append("missing=" + ",".join(missing[:3]))
        raise CacheMaterialDifference("cache data members differ from manifest (" + ";".join(detail) + ")",
                                      "extra-member" if extra else "missing-member", (extra or missing)[0])
    if small_files_first:
        expected = sorted(expected, key=lambda item: (actual[item["path"]], item["path"]))
    snapshot_phase(observations, "directory_shape", "finish", shape_started, sizes=actual)
    hash_started = snapshot_phase(observations, "declared_material_hash", "start")
    inventory = files(directory, expected=expected, parallel=not small_files_first,
                      parents_verified=private_staging)
    snapshot_phase(observations, "declared_material_hash", "finish", hash_started, sizes=actual)
    return inventory


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
        validate_cache_directory(staged, expected, private_staging=True)
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
    observations = ({name: {"status": "not-entered"} for name in
                     ("current_handoff_validation", "cache_lock_wait", "directory_shape", "declared_material_hash")}
                    if layer in LAYERS else None)
    current_materials = None
    if current is not None and layer in ("dependency", "project"):
        handoff_started = snapshot_phase(observations, "current_handoff_validation", "start")
        current_materials = current_lean_materials(root, *current)
        snapshot_phase(observations, "current_handoff_validation", "finish", handoff_started)
        if current_materials is None:
            metrics = {"save_disabled_reason": "current did not execute a successful Lean build",
                       "observations": observations}
            (staged / "metrics.json").write_text(json.dumps(metrics) + "\n")
            return metrics
    difference = {}
    judge_donor = None
    lock_started = snapshot_phase(observations, "cache_lock_wait", "start")
    with cache_guard(root, shared=True):
        snapshot_phase(observations, "cache_lock_wait", "finish", lock_started)
        reason = (restored_save_reason(root, spec, layer, keys["partition"], difference,
                                      current_materials=current_materials, observations=observations)
                  if layer in ("dependency", "project") else None)
        if reason:
            metrics = {"save_disabled_reason": reason, "observations": observations}
            (staged / "metrics.json").write_text(json.dumps(metrics) + "\n")
            return metrics
        if layer in EXECUTION_LAYERS:
            inventory = snapshot_execution(root, layer, keys, staged / "data")
        elif layer == "judge":
            sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "report"))
            from dotnet_producer import stage_seed, unique_object
            cached = root / spec["path"]
            donor = None
            if cached.exists():
                try:
                    previous = json.loads((cached / "manifest.json").read_text(), object_pairs_hook=unique_object)
                    if (not isinstance(previous, dict) or previous.get("schema") != "lean-actions-seed-v1"
                            or previous.get("partition") != keys["partition"] or previous.get("layer") != layer
                            or not isinstance(previous.get("key"), str)
                            or not re.fullmatch(re.escape(spec["restore_prefix"]) + r"[0-9]+-[0-9]+", previous["key"])):
                        raise ValueError("judge donor identity mismatch")
                    donor = cached / "data", files(cached / "data", expected=previous.get("files"))
                except (OSError, ValueError, KeyError, TypeError) as error:
                    judge_donor = {"status": "miss", "reason": str(error)}
            retained = stage_seed(root, staged / "data", registry, donor=donor)
            judge_donor = judge_donor or retained
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
    if observations is not None:
        metrics["observations"] = observations
    if difference:
        metrics["snapshot_reason"] = difference
    if judge_donor is not None:
        metrics["judge_donor"] = judge_donor
    (staged / "metrics.json").write_text(json.dumps(metrics, sort_keys=True) + "\n")
    return metrics


def restored_save_reason(root, spec, layer, partition, difference=None, *, current_materials=None, observations=None):
    """Choose whether to omit an optional save of a successfully restored seed.

    An accepted current report with the donor's input attestation can retain a
    project seed without comparing the whole build directory. This is a save
    policy, not evidence that its other bytes are unchanged. Otherwise preserve
    the full shape/mode/byte comparison, checking small files first.
    """
    manifest_path = root / spec["path"] / "manifest.json"
    restored_path = root / spec["path"] / "restored.json"
    def changed(reason, path=None):
        if difference is not None:
            difference.update({"reason": reason, **({"path": path} if path is not None else {})})
        return None

    try:
        if manifest_path.is_symlink() or restored_path.is_symlink():
            return changed("unsafe-cache-state")
        manifest_bytes = manifest_path.read_bytes()
        manifest = json.loads(manifest_bytes)
        restored = json.loads(restored_path.read_bytes())
        if (not isinstance(manifest, dict) or manifest.get("schema") != "lean-actions-seed-v1"
                or manifest.get("partition") != partition
                or manifest.get("layer") != layer
                or restored != {"schema": "lean-actions-restored-v1", "snapshot_key": spec["key"],
                                "manifest_sha256": hashlib.sha256(manifest_bytes).hexdigest()}):
            return changed("restore-record-mismatch")
        if layer == "project" and current_materials is not None:
            attestation = "stratalint/raw-lean-report.json.input.attestation"
            current_sha = current_materials.get(spec["target"] + "/" + attestation)
            validate_manifest(manifest.get("files"))
            if current_sha is not None and any(item["path"] == attestation and item["sha256"] == current_sha
                                               for item in manifest["files"]):
                return "retained-restored-seed"
        target = root / spec["target"]
        validate_cache_directory(target, manifest.get("files"), small_files_first=True, observations=observations)
        return "unchanged"
    except CacheMaterialDifference as error:
        return changed(error.reason, error.path)
    except OSError:
        return changed("cache-state-unavailable")
    except (ValueError, TypeError, KeyError, json.JSONDecodeError):
        return changed("invalid-cache-state")


def current_lean_materials(root, plan, commit):
    """Accept executed Lean work once; expose only its validated report material."""
    step = "lean-report" if "lean-report" in plan["execution"]["steps"] else "lean"
    if step not in plan["execution"]["steps"]:
        return None
    transport, current, report, accepted = accepted_current(root)
    if transport["commit"] != commit:
        raise ValueError("current Lean build belongs to another candidate")
    # Native report execution always requires the default Lean targets and
    # inspector build. An executed, accepted report therefore attests both.
    if step == "lean-report" and report is None:
        raise ValueError("current Lean build has no accepted native report")
    if any(item["name"] == step and item["status"] == "executed" and item["raw_exit"] == 0
           and item["exit"] == 0 for item in current["steps"]):
        return accepted if report is not None else {}
    return None


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
                receipt(layer, "save-disabled",
                        reason=deadline.reason if deadline.cutoff is None else "insufficient-cache-window",
                        remaining_seconds=round(deadline.remaining(), 3))
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
                    receipt(layer, "save-disabled", reason=metrics["save_disabled_reason"],
                            **({"observations": metrics["observations"]} if "observations" in metrics else {}))
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
        started = time.monotonic()
        try:
            spec = keys[layer]
            cached = root / spec["path"]
            restored_path = cached / "restored.json"
            restored_path.unlink(missing_ok=True)
            key = matched[layer]
            if not key:
                receipt(layer, "miss", reason="Actions supplied no cache",
                        elapsed_seconds=round(time.monotonic() - started, 3))
                continue
            if not re.fullmatch(re.escape(spec["restore_prefix"]) + r"[0-9]+-[0-9]+", key):
                raise ValueError("Actions seed is outside the selected partition")
            manifest_bytes = (cached / "manifest.json").read_bytes()
            manifest = json.loads(manifest_bytes)
            if (not isinstance(manifest, dict) or manifest.get("schema") != "lean-actions-seed-v1" or manifest.get("partition") != keys["partition"]
                    or manifest.get("layer") != layer or manifest.get("key") != key):
                raise ValueError("Actions seed identity or material integrity mismatch")
            stream_copy = layer in ("dependency", "project")
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
                        # Verify the exact bytes copied into private staging.
                        # Execution seeds then cross their native verifier.
                        staged.mkdir()
                        files(cached / "data", expected=manifest.get("files"), copy_to=staged)
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
            receipt(layer, "restored", key=key, partition=keys["partition"],
                    elapsed_seconds=round(time.monotonic() - started, 3))
        except (OSError, ValueError, TypeError, KeyError, subprocess.CalledProcessError) as error:
            receipt(layer, "miss", reason=str(error),
                    elapsed_seconds=round(time.monotonic() - started, 3))
    # A dependency-only hit cannot suppress the project Release fallback.
    if "project" in layers:
        output({"STRATALINT_ACTIONS_CACHE_SEEDED": "1" if project_seeded else "0"}, "GITHUB_ENV")


def report_seed(root, lake):
    """Ask the normal producer whether a transported full report can be reused.

    The check manifest declares the report paths; this adapter neither infers
    producer inputs nor treats a cache hit or prior check as current success.
    Publication and the second input/material validation belong to inspect.sh.
    """
    seed = root / "build/ci/current-check-seed"
    try:
        checks = json.loads((seed / "checks.json").read_text())
        if (checks.get("version") != 2 or checks.get("stage") != "current"
                or not re.fullmatch(r"[0-9a-f]{64}", checks.get("candidate", ""))
                or not re.fullmatch(r"[0-9a-f]{32}", checks.get("round", ""))):
            return None
        reports = set()
        suffixes = ("", ".sha256", ".input.attestation", ".provenance.json", ".materials.zip", ".reuse.json")
        for unit in checks["units"]:
            relative = unit.get("report")
            if not isinstance(relative, str) or not re.fullmatch(
                    r"build/ci/check-material/[0-9a-f]{64}/[0-9a-f]{32}/[0-9a-f]{32}/report/raw-lean-report\.json", relative):
                continue
            declared = {material["path"] for material in unit["materials"]}
            if all(relative + suffix in declared for suffix in suffixes):
                reports.add(relative)
    except (OSError, ValueError, TypeError, KeyError, AttributeError):
        return None
    for relative in sorted(reports):
        report = seed / relative
        result = subprocess.run([sys.executable, str(root / "tools/lean-inspector/reuse.py"), "probe",
            "--repository", str(root), "--report", str(report), "--lake", str(lake)],
            cwd=root, check=True, capture_output=True, text=True)
        outcome = json.loads(result.stdout)
        if type(outcome.get("needs_lake")) is not bool:
            raise ValueError("report producer returned no cache resource decision")
        if not outcome["needs_lake"]:
            return str(report)
    return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("keys", "restore", "snapshot", "prepare-report"))
    parser.add_argument("--repository", required=True, type=pathlib.Path)
    parser.add_argument("--layers", choices=ALL_LAYERS, nargs="+")
    parser.add_argument("--stage", choices=("build", "engineering", "current", "delta"))
    parser.add_argument("--layer", choices=ALL_LAYERS)
    parser.add_argument("--bounded-cache", action="store_true")
    parser.add_argument("--snapshot-directory", type=pathlib.Path, help=argparse.SUPPRESS)
    for layer in ALL_LAYERS:
        parser.add_argument("--" + layer + "-key", default="")
    args = parser.parse_args()
    if args.command == "prepare-report" and (args.stage != "current" or args.layer or args.layers):
        parser.error("prepare-report requires --stage current and its registered layer scope")
    if args.layer and args.layers:
        parser.error("--layer and --layers cannot be combined")
    if args.layer and not args.stage:
        parser.error("--layer requires --stage")
    if args.bounded_cache and (args.command != "snapshot" or not args.layer or args.stage not in ("build", "engineering", "current")):
        parser.error("--bounded-cache requires snapshot with --stage and --layer")
    if args.snapshot_directory and (args.command != "snapshot" or args.bounded_cache
            or not (args.stage == "current" and args.layer or not args.stage and len(args.layers or LAYERS) == 1)):
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
            registered_layers = requirements["cache_layers"]
            if args.layers is not None and (len(set(args.layers)) != len(args.layers)
                    or not set(args.layers).issubset(registered_layers)):
                raise ValueError("requested cache layers exceed the registered stage scope")
            args.layers = registered_layers if args.layers is None else args.layers
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
        if not args.layers and args.command != "prepare-report":
            return 0
    else:
        args.layers = list(LAYERS) if args.layers is None else args.layers
    current = (plan, commit) if args.command == "snapshot" and args.stage == "current" else None
    elan = "elan" in args.layers or args.stage is None
    args.layers = [layer for layer in args.layers if layer != "elan"]
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "report"))
    from dotnet_producer import ProjectRegistrationError
    if args.command == "prepare-report":
        # Registration/producer errors are required failures, not optional cache
        # failures. A missing or rejected seed simply keeps the normal resources.
        try:
            if "current" in args.layers:
                restore(args.repository, actions_keys(args.repository), {"current": args.current_key}, ["current"])
            source = None
            if "lean-report" in plan["execution"]["steps"]:
                lake = shutil.which("lake")
                if not lake:
                    raise ValueError("the registered Lean toolchain is unavailable")
                source = report_seed(args.repository, pathlib.Path(lake))
            output({"needs_lake": bool("lake" in requirements["tools"] and source is None)})
            output({"STRATALINT_LEAN_REPORT_REUSE": source or ""}, "GITHUB_ENV")
            return 0
        except (OSError, ValueError, TypeError, KeyError, subprocess.SubprocessError) as error:
            print("CI_INPUT_FAILED " + str(error), file=sys.stderr)
            return 2
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
