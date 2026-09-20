"""Native Actions build seeds and strictly verified execution evidence."""
from __future__ import annotations

import argparse
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
from cache_material import files, sha

LAYERS = ("dependency", "project")
# Execution evidence is opt-in; native engineering/current owners produce it.
EXECUTION_LAYERS = ("engineering", "current")
ALL_LAYERS = (*LAYERS, "judge", *EXECUTION_LAYERS, "elan")


class CachePathRegistrationError(ValueError):
    pass


def native_archive_paths(root, layers):
    """Actions receives only the explicitly registered native archive paths."""
    selected = set(layers) & set(LAYERS)
    if not selected:
        return {}
    manifest = "Meta/ci-cache-paths.json"

    def unique_object(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("duplicate field: " + key)
            result[key] = value
        return result

    try:
        import tomllib
        filemap = tomllib.loads((root / "Meta/FILEMAP.toml").read_text())
        rows = [row for row in filemap.get("files", []) if row.get("pattern") == manifest]
        if len(rows) != 1:
            raise ValueError("manifest must have one literal FILEMAP entry")
        registration = json.loads((root / manifest).read_text(), object_pairs_hook=unique_object)
        if (not isinstance(registration, dict) or set(registration) != {"schema_version", "layers"}
                or type(registration["schema_version"]) is not int or registration["schema_version"] != 1
                or not isinstance(registration["layers"], dict)
                or not set(registration["layers"]).issubset(LAYERS)):
            raise ValueError("invalid schema or layer")
        result = {}
        roots = {"dependency": ".lake/packages", "project": ".lake/build"}
        for layer in sorted(selected):
            paths = registration["layers"].get(layer)
            if not isinstance(paths, list) or not paths:
                raise ValueError("missing paths for " + layer)
            for path in paths:
                if (not isinstance(path, str) or not re.fullmatch(r"[A-Za-z0-9_./*\-]+", path)
                        or any(part in ("", ".", "..") for part in path.split("/"))
                        or not (path == roots[layer] or path.startswith(roots[layer] + "/"))):
                    raise ValueError("invalid path for " + layer + ": " + repr(path))
            if len(set(paths)) != len(paths):
                raise ValueError("duplicate paths for " + layer)
            result[layer] = sorted(paths)
        return result
    except (OSError, ValueError, TypeError, AttributeError) as error:
        raise CachePathRegistrationError(f"cache path registration {manifest}: {error}") from error


def output_archive_paths(layer, paths):
    key = layer + "_archive_path"
    value = "\n".join(paths)
    delimiter = "STRATALINT_" + hashlib.sha256(value.encode()).hexdigest()
    if os.environ.get("GITHUB_OUTPUT"):
        with open(os.environ["GITHUB_OUTPUT"], "a", encoding="utf-8") as stream:
            stream.write(f"{key}<<{delimiter}\n{value}\n{delimiter}\n")
    # Keep diagnostic stdout line-oriented; the Actions command file carries
    # the actual multiline value consumed by both restore and save.
    print(key + "=" + json.dumps(paths, separators=(",", ":")))


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
        version = 4 if layer in LAYERS else 3
        prefix = f"lean-{layer}-v{version}-{revision}-{system}-{machine}-"
        result[layer] = {"restore_prefix": prefix, "key": f"{prefix}{run}-{attempt}",
                         "path": path if layer in LAYERS else "build/lean-cache/" + layer, "target": path}
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


def snapshot_execution(root, layer, keys, destination, *, seed_manifest=None):
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
    identity = ["--stage", spec["stage"], "--commit", commit,
                "--run-id", os.environ["GITHUB_RUN_ID"],
                "--run-attempt", os.environ["GITHUB_RUN_ATTEMPT"]]

    def verify(directory):
        try:
            subprocess.run(["dotnet", str(runner), "transport-verify", "--repository", str(directory), *identity],
                           cwd=root, check=True, capture_output=True, text=True)
        except subprocess.CalledProcessError as error:
            detail = (error.stderr or error.stdout or str(error)).strip()
            raise ValueError("native execution transport rejected prepared seed: " + detail) from error

    if seed_manifest is not None:
        # Ordinary pack retained an independent snapshot of its native manifest.
        # Copy its declared material directly from the accepted producer tree.
        clean_current_candidate(root, commit)
        verify(root)
        transport_path = "build/ci/" + spec["stage"] + "-transport.json"
        producer_manifest = root / transport_path
        prepared_transport_sha = sha(producer_manifest)
        if seed_manifest.is_symlink() or not seed_manifest.is_file():
            raise ValueError("prepared seed manifest is not a regular file")
        if sha(seed_manifest) != prepared_transport_sha:
            raise ValueError("prepared seed differs from producer transport")
        transport = json.loads(producer_manifest.read_text())
        expected = [*transport["materials"], {"path": transport_path,
            "sha256": prepared_transport_sha, "mode": producer_manifest.stat().st_mode & 0o777}]
        # Native validation owns the complete material list. copy_hash checks
        # exactly the bytes and modes copied, including any late source change.
        inventory = files(root, expected=expected, copy_to=destination)
        verify(destination)
        return inventory

    descriptor, archive_name = tempfile.mkstemp(prefix=f".{layer}-transport-", suffix=".tgz", dir=destination.parent)
    os.close(descriptor)
    archive = pathlib.Path(archive_name)
    try:
        command = ["dotnet", str(runner), "transport-pack", "--repository", str(root),
                   *identity, "--archive", str(archive)]
        try:
            subprocess.run(command, cwd=root, check=True, capture_output=True, text=True)
        except subprocess.CalledProcessError as error:
            status = subprocess.run(["git", "-C", str(root), "status", "--porcelain", "--untracked-files=all"], capture_output=True, text=True)
            detail = (error.stderr or error.stdout or str(error)).strip()
            raise ValueError(detail + ("; status=" + status.stdout.strip() if status.stdout.strip() else "")) from error
        with tarfile.open(archive, "r:gz") as source:
            seen = set()
            for member in source.getmembers():
                path = pathlib.PurePosixPath(member.name)
                if (not member.isfile() or path.is_absolute() or member.name in seen
                        or any(part in ("", ".", "..") for part in member.name.split("/"))):
                    raise ValueError("native execution transport contains an invalid member")
                seen.add(member.name)
                target = destination / path
                target.parent.mkdir(parents=True, exist_ok=True)
                with source.extractfile(member) as stream:
                    if stream is None:
                        raise ValueError("native execution transport member has no data")
                    target.write_bytes(stream.read())
                if os.name != "nt":
                    target.chmod(member.mode & 0o7777)
    except (tarfile.TarError, EOFError) as error:
        raise ValueError("invalid native execution archive: " + str(error)) from error
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


def stage_snapshot(root, keys, layer, staged, registry=None, *, current=None, seed_manifest=None):
    """Produce a private layer; only the parent may publish it and report ready."""
    spec = keys[layer]
    observations = ({name: {"status": "not-entered"} for name in
                     ("current_handoff_validation",)}
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
    if layer in LAYERS:
        target = root / spec["path"]
        if target.is_symlink() or not target.is_dir():
            raise ValueError("native cache directory is unavailable: " + spec["path"])
        metrics = {"transport": "actions-native", "observations": observations}
        if layer == "dependency":
            fingerprint = dependency_inputs(root)
            metrics["dependency_inputs_sha256"] = fingerprint
            try:
                restored = json.loads(dependency_restored_record(root).read_text())
                if (restored.get("snapshot_key") == spec["key"]
                        and re.fullmatch(re.escape(spec["restore_prefix"]) + r"[0-9]+-[0-9]+", restored.get("matched_key", ""))
                        and restored.get("inputs_sha256") == fingerprint):
                    metrics["save_disabled_reason"] = "retained-restored-dependency"
            except (OSError, ValueError, TypeError, AttributeError):
                pass
        (staged / "metrics.json").write_text(json.dumps(metrics) + "\n")
        return metrics
    judge_donor = None
    with cache_guard(root, shared=True):
        if layer in EXECUTION_LAYERS:
            inventory = snapshot_execution(root, layer, keys, staged / "data",
                                           **({"seed_manifest": seed_manifest} if seed_manifest is not None else {}))
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
    manifest = {"schema": "lean-actions-seed-v1", "partition": keys["partition"], "layer": layer,
                "key": spec["key"], "files": inventory}
    (staged / "manifest.json").write_text(json.dumps(manifest, sort_keys=True) + "\n")
    sizes = [(item, (staged / "data" / item["path"]).stat().st_size) for item in inventory]
    metrics = {"file_count": len(inventory), "uncompressed_bytes": sum(size for _, size in sizes),
               "largest_files": [{"path": item["path"], "sha256": item["sha256"], "size_bytes": size}
                                 for item, size in sorted(sizes, key=lambda pair: (-pair[1], pair[0]["path"]))[:5]]}
    if observations is not None:
        metrics["observations"] = observations
    if judge_donor is not None:
        metrics["judge_donor"] = judge_donor
    (staged / "metrics.json").write_text(json.dumps(metrics, sort_keys=True) + "\n")
    return metrics


def dependency_restored_record(root):
    return root / "build/lean-cache/dependency-restored.json"


def dependency_inputs(root):
    """Small registered save policy; never a cache key or a build verdict."""
    import tomllib
    registration = tomllib.loads((root / "Meta/FILEMAP.toml").read_text())
    rows = [row for row in registration["resources"] if row["id"] == "lean"]
    if len(rows) != 1:
        raise ValueError("dependency save requires the registered Lean resource")
    declared = rows[0]["materials"]
    required = {"lake-manifest.json", "lean-toolchain", "lakefile.toml"}
    if not required.issubset(declared):
        raise ValueError("dependency save configuration is not registered")
    paths = sorted(required | ({"lakefile.lean"} if "lakefile.lean" in declared else set()))
    inputs = {}
    for relative in paths:
        file = root / relative
        if file.is_symlink() or not file.is_file():
            raise ValueError("dependency save input is unavailable: " + relative)
        inputs[relative] = sha(file)
    declaration = json.loads((root / "lean-report-inputs.json").read_text())
    names = declaration["report_execution"]["environment"]
    if (not isinstance(names, list) or any(not isinstance(name, str) or not name for name in names)
            or len(set(names)) != len(names)):
        raise ValueError("dependency save environment registration is invalid")
    value = {"files": inputs, "environment": {name: os.environ.get(name) for name in names}}
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def write_small_record(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, name = tempfile.mkstemp(prefix=".actions-inputs-", dir=path.parent)
    temporary = pathlib.Path(name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            json.dump(value, stream)
            stream.write("\n")
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


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


def bounded_snapshot(root, layer, staged, seconds, *, current=False, seed_manifest=None):
    command = [sys.executable, str(pathlib.Path(__file__).resolve()), "snapshot", "--repository", str(root),
               *(["--stage", "current", "--layer", layer] if current else ["--layers", layer]),
               "--snapshot-directory", str(staged)]
    if seed_manifest is not None:
        command += ["--seed-manifest", str(seed_manifest)]
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


def snapshot(root, keys, layers=LAYERS, registry=None, *, deadline=None, current=None, seed_manifest=None):
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
            target = root / ("build/lean-cache" if layer in LAYERS else spec["path"])
            target.parent.mkdir(parents=True, exist_ok=True)
            with tempfile.TemporaryDirectory(prefix=".snapshot-", dir=target.parent) as temporary:
                staged = pathlib.Path(temporary)
                if deadline is None:
                    metrics = stage_snapshot(root, keys, layer, staged, registry, current=current, seed_manifest=seed_manifest)
                else:
                    bounded_snapshot(root, layer, staged, seconds, current=current is not None, seed_manifest=seed_manifest)
                    save_minutes = deadline.save_timeout_minutes()
                    if not save_minutes:
                        raise ValueError("snapshot left no cache save window")
                    metrics = json.loads((staged / "metrics.json").read_text())
                if "save_disabled_reason" in metrics:
                    receipt(layer, "save-disabled", reason=metrics["save_disabled_reason"],
                            **({"observations": metrics["observations"]} if "observations" in metrics else {}))
                    continue
                if layer in LAYERS:
                    if layer == "dependency":
                        write_small_record(root / spec["path"] / ".stratalint-actions-inputs.json",
                                           {"inputs_sha256": metrics["dependency_inputs_sha256"]})
                else:
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
    """Record the partition after Actions reports a matching dependency seed.

    This records partition identity only, just like the C# producer's stamp.
    It does not attest cache completeness or a successful build/report.
    Native Actions owns directory transport; this small record is atomic.
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


def restore_native(root, keys, layer, key, outcome):
    spec = keys[layer]
    target = root / spec["path"]
    if layer == "dependency":
        dependency_restored_record(root).unlink(missing_ok=True)
    # A skipped/missing Action has not written this directory. Preserve any
    # independently restored current evidence already under the build path.
    if outcome in ("", "skipped"):
        receipt(layer, "miss", reason="Actions supplied no cache")
        return False
    try:
        if outcome != "success":
            raise ValueError("Actions restore did not succeed: " + outcome)
        if not key:
            raise ValueError("Actions supplied no matched cache")
        if not re.fullmatch(re.escape(spec["restore_prefix"]) + r"[0-9]+-[0-9]+", key):
            raise ValueError("Actions seed is outside the selected partition")
        if target.is_symlink() or not target.is_dir():
            raise ValueError("native Actions cache directory is unavailable")
        if layer == "dependency":
            stamp_restored_dependency(root, keys)
            # The receipt affects only optional saving. Missing/invalid save
            # metadata does not invalidate a native incremental build seed.
            try:
                receipt_path = target / ".stratalint-actions-inputs.json"
                if receipt_path.is_symlink():
                    raise ValueError("dependency save receipt is a symlink")
                previous = json.loads(receipt_path.read_text())
                digest = previous["inputs_sha256"]
                if not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
                    raise ValueError("invalid dependency save inputs")
                write_small_record(dependency_restored_record(root), {
                    "snapshot_key": spec["key"], "matched_key": key, "inputs_sha256": digest})
            except (OSError, ValueError, TypeError, KeyError):
                pass
        receipt(layer, "restored", key=key, partition=keys["partition"], transport="actions-native")
        return True
    except (OSError, ValueError, TypeError) as error:
        # A failed Action may have extracted a partial archive. Remove only
        # its registered layer before the required producer starts.
        if target.is_symlink() or target.is_file():
            target.unlink()
        elif target.exists():
            shutil.rmtree(target)
        receipt(layer, "miss", reason=str(error))
        return False


def restore(root, keys, matched, layers=LAYERS, registry=None, *, outcomes=None):
    if registry is None:
        validate_judge_registration(root, layers)
    project_seeded = False
    for layer in layers:
        started = time.monotonic()
        try:
            spec = keys[layer]
            key = matched[layer]
            if layer in LAYERS:
                accepted = restore_native(root, keys, layer, key, (outcomes or {}).get(layer, ""))
                project_seeded |= layer == "project" and accepted
                continue
            cached = root / spec["path"]
            if not key:
                receipt(layer, "miss", reason="Actions supplied no cache",
                        elapsed_seconds=round(time.monotonic() - started, 3))
                continue
            if not re.fullmatch(re.escape(spec["restore_prefix"]) + r"[0-9]+-[0-9]+", key):
                raise ValueError("Actions seed is outside the selected partition")
            manifest = json.loads((cached / "manifest.json").read_text())
            if (not isinstance(manifest, dict) or manifest.get("schema") != "lean-actions-seed-v1"
                    or manifest.get("partition") != keys["partition"]
                    or manifest.get("layer") != layer or manifest.get("key") != key):
                raise ValueError("Actions seed identity or material integrity mismatch")
            target = root / spec.get("target", ".")
            with cache_guard(root):
                target.parent.mkdir(parents=True, exist_ok=True)
                with tempfile.TemporaryDirectory(prefix=".actions-", dir=target.parent) as temporary:
                    staged = pathlib.Path(temporary) / "data"
                    staged.mkdir()
                    files(cached / "data", expected=manifest.get("files"), copy_to=staged)
                    if layer in EXECUTION_LAYERS:
                        restore_execution(root, layer, keys, staged)
                    else:
                        replace_restored_directory(staged, target, pathlib.Path(temporary) / "rollback")
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

    The seed manifest declares the report paths; this adapter neither infers
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
        producer_path = seed / "producer-report.json"
        if producer_path.exists():
            producer = json.loads(producer_path.read_text())
            relative = ".lake/build/stratalint/raw-lean-report.json"
            if (set(producer) != {"version", "candidate", "round", "report", "materials"}
                    or producer["version"] != 1 or producer["report"] != relative
                    or not re.fullmatch(r"[0-9a-f]{64}", producer["candidate"])
                    or not re.fullmatch(r"[0-9a-f]{32}", producer["round"])):
                return None
            declared = [material["path"] for material in producer["materials"]]
            if len(declared) != len(suffixes) or set(declared) != {relative + suffix for suffix in suffixes}:
                return None
            reports.add(relative)
        else:
            # Legacy seeds carry only the original report of each check unit.
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
    parser.add_argument("--seed-manifest", help="reuse this execution's native sealed seed manifest")
    parser.add_argument("--snapshot-directory", type=pathlib.Path, help=argparse.SUPPRESS)
    for layer in ALL_LAYERS:
        parser.add_argument("--" + layer + "-key", default="")
    for layer in LAYERS:
        parser.add_argument("--" + layer + "-outcome", default="",
                            choices=("", "success", "failure", "cancelled", "skipped"))
    args = parser.parse_args()
    args.seed_manifest = pathlib.Path(args.seed_manifest).absolute() if args.seed_manifest else None
    if args.seed_manifest is not None:
        selected = [args.layer] if args.layer else args.layers
        if args.command != "snapshot" or not selected or len(selected) != 1 or selected[0] not in EXECUTION_LAYERS:
            parser.error("--seed-manifest requires snapshot with one explicit execution layer")
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
            output({"needs_lake": bool("lake" in requirements["tools"]
                and (source is None or plan["execution"]["lean_targets"]))})
            output({"STRATALINT_LEAN_REPORT_REUSE": source or ""}, "GITHUB_ENV")
            return 0
        except (OSError, ValueError, TypeError, KeyError, subprocess.SubprocessError) as error:
            print("CI_INPUT_FAILED " + str(error), file=sys.stderr)
            return 2
    try:
        archive_paths = native_archive_paths(args.repository, args.layers) if args.command == "keys" else {}
        registry = validate_judge_registration(args.repository, args.layers) if args.command != "keys" else None
        keys = actions_keys(args.repository)
        if args.snapshot_directory:
            stage_snapshot(args.repository, keys, args.layers[0], args.snapshot_directory, registry,
                           current=current, seed_manifest=args.seed_manifest)
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
            for layer, paths in archive_paths.items():
                output_archive_paths(layer, paths)
        elif args.command == "restore":
            restore(args.repository, keys, {layer: getattr(args, layer + "_key") for layer in args.layers}, args.layers, registry,
                    outcomes={layer: getattr(args, layer + "_outcome") for layer in LAYERS})
        else:
            deadline = None
            if args.bounded_cache:
                from cache_deadline import load_deadline
                deadline = load_deadline(args.repository, args.stage)
            snapshot(args.repository, keys, args.layers, registry, deadline=deadline,
                     current=current, seed_manifest=args.seed_manifest)
        return 0
    except (ProjectRegistrationError, CachePathRegistrationError) as error:
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
