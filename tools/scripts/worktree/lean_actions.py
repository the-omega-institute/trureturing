"""Actions snapshots are optional, integrity-checked inputs to normal producers."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
import tarfile

from lean_cache import binary_platform, partition_path, resolved_mathlib
from lean_cache_release import cache_guard
from cache_material import files, sha

LAYERS = ("dependency", "project", "report")
# Execution evidence is deliberately opt-in.  The existing default cache
# layers remain unchanged; callers request these layers when the native
# engineering/current seed owners have produced their exports.
EXECUTION_LAYERS = ("engineering", "current")
ALL_LAYERS = (*LAYERS, "judge", *EXECUTION_LAYERS)


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
                  and os.environ.get("GITHUB_REF") in (
                      "refs/heads/dev",
                      # Integration-only rollout binding; exclude from dev delivery.
                      "refs/heads/integration-ci-current-stability-0909-tests")
                  and os.environ.get("STRATALINT_CACHE_WRITES", "true") == "true")
    result = {"mathlib_revision": revision, "os": system, "arch": machine,
              "partition": partition_path(root),
              "save_allowed": writer_allowed and os.environ.get("STRATALINT_CHECK_SUCCEEDED") == "true",
              # A compilation seed attests production, never engineering/current checks.
              "judge_save_allowed": writer_allowed and os.environ.get("STRATALINT_BUILD_SUCCEEDED") == "true"}
    paths = {"dependency": ".lake/packages", "project": ".lake/build",
             "report": ".lake/report-cache", "judge": ".judge-binaries"}
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


def snapshot_report(root, partition, destination):
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "lean-inspector"))
    from report_cache import SUFFIXES, copy_bundle, member, seed_identity
    from delta import validate_report_sha

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
    relative = summary["report"]
    if pathlib.PurePosixPath(relative).is_absolute() or any(part in ("", ".", "..") for part in relative.split("/")):
        raise ValueError("invalid current report path")
    accepted = {item["path"]: item["sha256"] for item in current["materials"]}
    if len(accepted) != len(current["materials"]):
        raise ValueError("duplicate current material")
    for suffix in SUFFIXES:
        path = relative + suffix
        full = root / path
        mode = 0 if os.name == "nt" else full.stat().st_mode & 0o7777
        if (full.is_symlink() or not full.is_file() or accepted[path] != transported[path]["sha256"]
                or mode != transported[path]["mode"]):
            raise ValueError("current report member mismatch: " + path)
    report = root / relative
    bound_bytes(relative + ".sha256")
    validate_report_sha(report, accepted[relative])
    seed = json.loads(bound_bytes(relative + ".seed.json"))
    if not isinstance(seed, dict) or seed.get("partition") != partition:
        raise ValueError("current report partition mismatch")
    bound_bytes(relative + ".provenance.json")
    destination.mkdir(mode=0o700)
    staged = destination / partition / seed_identity(report) / "raw-lean-report.json"
    copy_bundle(report, staged)
    inventory = files(destination)
    expected = {member(staged, suffix).relative_to(destination).as_posix(): accepted[relative + suffix]
                for suffix in SUFFIXES}
    expected[member(staged, ".sha256").relative_to(destination).as_posix()] = hashlib.sha256(
        f"{accepted[relative]}  {staged.name}\n".encode()).hexdigest()
    if {item["path"]: item["sha256"] for item in inventory} != expected:
        raise ValueError("staged report differs from accepted current material")
    for args, expected_output in ((["rev-parse", "HEAD"], transport["commit"]),
                                  (["status", "--porcelain", "--untracked-files=all"], "")):
        result = subprocess.run(["git", "-C", str(root), *args], capture_output=True, text=True)
        if result.returncode or result.stdout.strip() != expected_output:
            raise ValueError("report snapshot requires the exact clean candidate commit")
    return inventory


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


def snapshot(root, keys, layers=LAYERS, registry=None):
    registry = registry if registry is not None else validate_judge_registration(root, layers)
    for layer in layers:
        ready = False
        try:
            if not keys["judge_save_allowed" if layer == "judge" else "save_allowed"]:
                receipt(layer, "save-disabled")
                continue
            spec = keys[layer]
            target = root / spec["path"]
            target.parent.mkdir(parents=True, exist_ok=True)
            with tempfile.TemporaryDirectory(prefix=".snapshot-", dir=target.parent) as temporary:
                staged = pathlib.Path(temporary)
                with cache_guard(root, shared=True):
                    if layer in EXECUTION_LAYERS:
                        inventory = snapshot_execution(root, layer, keys, staged / "data")
                    elif layer == "report":
                        inventory = snapshot_report(root, keys["partition"], staged / "data")
                    elif layer == "judge":
                        sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "report"))
                        from dotnet_producer import stage_seed
                        stage_seed(root, staged / "data", registry)
                    else:
                        shutil.copytree(root / spec["target"], staged / "data", symlinks=True)
                if layer != "report":
                    inventory = files(staged / "data", materialize_links=layer == "dependency")
                manifest = {"schema": "lean-actions-seed-v1", "partition": keys["partition"], "layer": layer,
                            "key": spec["key"], "files": inventory}
                (staged / "manifest.json").write_text(json.dumps(manifest, sort_keys=True) + "\n")
                if target.exists():
                    shutil.rmtree(target)
                staged.rename(target)
                ready = True
                receipt(layer, "snapshot", key=spec["key"])
        except (OSError, ValueError, TypeError, KeyError) as error:
            receipt(layer, "save-failed", reason=str(error))
        finally:
            output({layer + "_ready": ready})


def restore(root, keys, matched, layers=LAYERS, registry=None):
    if registry is None:
        validate_judge_registration(root, layers)
    project_seeded = False
    for layer in layers:
        try:
            spec, key = keys[layer], matched[layer]
            if not key:
                receipt(layer, "miss", reason="Actions supplied no cache")
                continue
            if not re.fullmatch(re.escape(spec["restore_prefix"]) + r"[0-9]+-[0-9]+", key):
                raise ValueError("Actions seed is outside the selected partition")
            cached = root / spec["path"]
            manifest = json.loads((cached / "manifest.json").read_text())
            if (not isinstance(manifest, dict) or manifest.get("schema") != "lean-actions-seed-v1" or manifest.get("partition") != keys["partition"]
                    or manifest.get("layer") != layer or manifest.get("key") != key
                    or manifest.get("files") != files(cached / "data", expected=manifest["files"])):
                raise ValueError("Actions seed identity or material integrity mismatch")
            target = root / spec.get("target", ".")
            with cache_guard(root):
                target.parent.mkdir(parents=True, exist_ok=True)
                with tempfile.TemporaryDirectory(prefix=".actions-", dir=target.parent) as temporary:
                    staged = pathlib.Path(temporary) / "data"
                    # Copy exactly the validated manifest; unlisted neighbours
                    # cannot introduce projects or executable seed material.
                    staged.mkdir()
                    for item in manifest["files"]:
                        destination = staged / item["path"]
                        destination.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copy2(cached / "data" / item["path"], destination)
                    if layer == "report":
                        sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "lean-inspector"))
                        from report_cache import seed_valid
                        reports = [staged / item["path"] for item in manifest["files"]
                                   if pathlib.PurePosixPath(item["path"]).name == "raw-lean-report.json"
                                   and pathlib.PurePosixPath(item["path"]).parent.parent.as_posix() == keys["partition"]]
                        if not reports or not any(seed_valid(report, keys["partition"]) for report in reports):
                            raise ValueError("Actions report cache has no valid complete seed")
                    if layer in EXECUTION_LAYERS:
                        restore_execution(root, layer, keys, staged)
                    else:
                        if target.exists():
                            shutil.rmtree(target)
                        staged.rename(target)
            project_seeded |= layer == "project"
            receipt(layer, "restored", key=key, partition=keys["partition"])
        except (OSError, ValueError, TypeError, KeyError, subprocess.CalledProcessError) as error:
            receipt(layer, "miss", reason=str(error))
    # Release supplies the project layer. Dependency-only and report-only hits
    # must not suppress a missing project layer's same-partition fallback.
    if "project" in layers:
        output({"STRATALINT_ACTIONS_CACHE_SEEDED": "1" if project_seeded else "0"}, "GITHUB_ENV")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("keys", "restore", "snapshot"))
    parser.add_argument("--repository", required=True, type=pathlib.Path)
    parser.add_argument("--layers", choices=ALL_LAYERS, nargs="+", default=LAYERS)
    for layer in ALL_LAYERS:
        parser.add_argument("--" + layer + "-key", default="")
    args = parser.parse_args()
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "report"))
    from dotnet_producer import ProjectRegistrationError
    try:
        registry = validate_judge_registration(args.repository, args.layers) if args.command != "keys" else None
        keys = actions_keys(args.repository)
        if args.command == "keys":
            values = {}
            values.update({key: keys[key] for key in
                           ("mathlib_revision", "os", "arch", "partition", "save_allowed", "judge_save_allowed", "release_prefix")})
            for layer in args.layers:
                values.update({layer + "_" + key: value for key, value in keys[layer].items()})
            system, arch = binary_platform()
            toolchain = hashlib.sha256((args.repository / "lean-toolchain").read_bytes()).hexdigest()
            values["elan_key"] = f"elan-v1-{system}-{arch}-{toolchain}"
            output(values)
        elif args.command == "restore":
            restore(args.repository, keys, {layer: getattr(args, layer + "_key") for layer in args.layers}, args.layers, registry)
        else:
            snapshot(args.repository, keys, args.layers, registry)
        return 0
    except ProjectRegistrationError as error:
        print(str(error), file=sys.stderr)
        return 2
    except (OSError, ValueError, TypeError, KeyError, subprocess.CalledProcessError) as error:
        receipt("all", "unavailable", reason=str(error))
        if args.command == "restore" and "project" in args.layers:
            output({"STRATALINT_ACTIONS_CACHE_SEEDED": "0"}, "GITHUB_ENV")
        return 0


if __name__ == "__main__":
    raise SystemExit(main())
