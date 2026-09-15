"""Durable report planning outside replaceable Lean caches; delta owns decisions."""
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

sys.dont_write_bytecode = True
from runtime_identity import file_sha, registration, runtime_hash, select_binaries
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "scripts/worktree"))
from lean_cache import partition_path

HEX = re.compile(r"[0-9a-f]{64}")
SCHEMA = "lean-report-preparation-v1"
RESULT_SCHEMA = "lean-report-preparation-result-v1"
IDENTITY = {"input_address", "repository_sha256", "producer_sha256", "sources_sha256", "config_sha256"}
FIELDS = {"schema", "repository", "lake", "lean", "runtime_sha256", "partition", "plan_sha256",
    "modules_sha256", "needs_lean_build", "seed_sha256", *IDENTITY}
RESULT_FIELDS = {"schema", "input_address", "runtime_sha256", "partition", "report_sha256",
    "lean_build_executed", "lean_build_succeeded"}
# These are the only baseline materials consumed by delta.merge. The planner
# validates the original bundle; these fixed copies survive cache replacement.
SEED_FILES = ("baseline/raw-lean-report.json", "baseline/raw-lean-report.json.materials.zip")


def write_json(path: pathlib.Path, value: dict) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, sort_keys=True) + "\n")
    temporary.replace(path)


def read_json(path: pathlib.Path) -> dict:
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate key in {path.name}: {key}")
            result[key] = value
        return result
    value = json.loads(path.read_text(), object_pairs_hook=unique)
    if not isinstance(value, dict):
        raise ValueError(f"{path.name} must be an object")
    return value


def input_identity(root: pathlib.Path) -> dict:
    helper = root / "tools/scripts/report/lean-report-input.sh"
    value = subprocess.run([str(helper), "address", "--repository", str(root)],
        check=True, capture_output=True, text=True)
    parts = value.stdout.strip().split(" ")
    if len(parts) != 4 or any(HEX.fullmatch(part) is None for part in parts):
        raise ValueError("repository input address is malformed")
    repository, producer, sources, config = parts
    preimage = ("schema=stratalint-lean-report-input-v1\n" + f"producer_sha256={producer}\n"
        + f"repository_inspector_sha256={producer}\n" + f"lean_sources_sha256={sources}\n"
        + f"lean_config_sha256={config}\n")
    return dict(input_address=hashlib.sha256(preimage.encode()).hexdigest(), repository_sha256=repository,
        producer_sha256=producer, sources_sha256=sources, config_sha256=config)


def location(root: pathlib.Path, directory: pathlib.Path) -> pathlib.Path:
    if not directory.is_absolute() or directory.resolve().is_relative_to((root / ".lake").resolve()):
        raise ValueError("report preparation must be an absolute directory outside .lake")
    return directory.resolve()


def trusted_cache(cache: pathlib.Path) -> bool:
    try:
        info = cache.stat()
        return cache.is_dir() and info.st_uid == os.getuid() and not info.st_mode & 0o022
    except OSError:
        return False


def plan_requires_build(plan: dict) -> bool:
    if plan.get("status") not in ("fallback", "reuse", "delta"):
        raise ValueError("prepared delta plan status is invalid")
    if plan["status"] == "fallback":
        return True
    for name in ("recheck", "changed", "added", "removed"):
        items = plan.get(name)
        if not isinstance(items, list) or any(not isinstance(item, str) or not item for item in items):
            raise ValueError(f"prepared delta plan {name} is invalid")
    return bool(plan["recheck"])


def prepare(root: pathlib.Path, directory: pathlib.Path, lake: str = "", lean: str = "") -> dict:
    root = root.resolve()
    directory = location(root, directory)
    registration(root)
    binaries = select_binaries(root, lake, lean)
    identity = input_identity(root)
    runtime = runtime_hash(root, binaries[1])
    partition = partition_path(root)
    directory.mkdir(parents=True, exist_ok=True)
    if any(directory.iterdir()):
        raise ValueError("report preparation directory must be empty")
    modules = directory / "modules.tsv"
    with modules.open("w") as output:
        subprocess.run([str(root / "tools/scripts/report/lean-report-input.sh"), "modules",
            "--repository", str(root)], check=True, stdout=output)
    plan_path = directory / "delta-plan.json"
    plan = {"status": "fallback"}
    cache_value = os.environ.get("STRATALINT_REPORT_CACHE_ROOT", "")
    cache = pathlib.Path(cache_value).resolve() if cache_value else None
    if cache is not None and trusted_cache(cache):
        command = [sys.executable, str(root / "tools/lean-inspector/delta.py"), "plan", str(root),
            str(cache / partition), identity["input_address"], identity["producer_sha256"],
            identity["producer_sha256"], identity["config_sha256"], str(modules), str(plan_path),
            "--runtime-sha", runtime, "--partition", partition]
        try:
            subprocess.run(command, check=True, stdout=sys.stderr)
            plan = read_json(plan_path)
            plan_requires_build(plan)
        except (OSError, ValueError, subprocess.CalledProcessError) as error:
            print(f"LEAN_REPORT_PREPARATION seed_plan=fallback reason={error}", file=sys.stderr)
            plan = {"status": "fallback"}
    seed_hashes = {}
    if plan["status"] in ("reuse", "delta"):
        try:
            baseline = pathlib.Path(plan["baseline"])
            fixed = directory / SEED_FILES[0]
            fixed.parent.mkdir()
            shutil.copyfile(baseline, fixed)
            shutil.copyfile(pathlib.Path(str(baseline) + ".materials.zip"), directory / SEED_FILES[1])
            seed_hashes = {name: file_sha(directory / name) for name in SEED_FILES}
            if seed_hashes[SEED_FILES[0]] != plan["baseline_report_sha256"]:
                raise ValueError("selected report changed while preparing")
            plan["baseline"] = str(fixed)
        except (OSError, ValueError, KeyError) as error:
            print(f"LEAN_REPORT_PREPARATION seed_copy=fallback reason={error}", file=sys.stderr)
            plan, seed_hashes = {"status": "fallback"}, {}
    write_json(plan_path, plan)
    state = dict(schema=SCHEMA, repository=str(root), lake=binaries[0], lean=binaries[1],
        runtime_sha256=runtime, partition=partition, plan_sha256=file_sha(plan_path),
        modules_sha256=file_sha(modules), needs_lean_build=plan_requires_build(plan),
        seed_sha256=seed_hashes, **identity)
    write_json(directory / "preparation.json", state)
    return state


def descriptor(root: pathlib.Path, directory: pathlib.Path) -> tuple[dict, dict]:
    state = read_json(directory / "preparation.json")
    if (set(state) != FIELDS or state["schema"] != SCHEMA or state["repository"] != str(root)
            or type(state["needs_lean_build"]) is not bool
            or any(not isinstance(state[name], str) or HEX.fullmatch(state[name]) is None
                for name in (*IDENTITY, "runtime_sha256", "plan_sha256", "modules_sha256"))):
        raise ValueError("report preparation descriptor is malformed or belongs to another candidate")
    for name, field in (("delta-plan.json", "plan_sha256"), ("modules.tsv", "modules_sha256")):
        if file_sha(directory / name) != state[field]:
            raise ValueError(f"report preparation {name} integrity mismatch")
    plan = read_json(directory / "delta-plan.json")
    if plan_requires_build(plan) != state["needs_lean_build"]:
        raise ValueError("report preparation build decision mismatch")
    expected_seeds = set(SEED_FILES) if plan["status"] in ("reuse", "delta") else set()
    if (not isinstance(state["seed_sha256"], dict) or set(state["seed_sha256"]) != expected_seeds
            or any(not isinstance(value, str) or HEX.fullmatch(value) is None for value in state["seed_sha256"].values())
            or expected_seeds and plan.get("baseline") != str(directory / SEED_FILES[0])):
        raise ValueError("report preparation fixed seed identity is malformed")
    return state, plan


def validate(root: pathlib.Path, directory: pathlib.Path) -> dict:
    root = pathlib.Path(root).resolve()
    directory = location(root, pathlib.Path(directory))
    state, _ = descriptor(root, directory)
    if (any(state[name] != value for name, value in input_identity(root).items())
            or state["partition"] != partition_path(root)
            or state["runtime_sha256"] != runtime_hash(root, state["lean"])):
        raise ValueError("report preparation does not match current candidate inputs/runtime/partition")
    select_binaries(root, state["lake"], state["lean"])
    return state


def execution_plan(directory: pathlib.Path, state: dict, output: pathlib.Path) -> None:
    plan = read_json(directory / "delta-plan.json")
    try:
        for name, digest in state["seed_sha256"].items():
            if file_sha(directory / name) != digest:
                raise ValueError(f"fixed seed material changed: {name}")
    except (OSError, ValueError) as error:
        print(f"LEAN_REPORT_PREPARATION seed_resume=fallback reason={error}", file=sys.stderr)
        plan = {"status": "fallback"}
    write_json(output, plan)
    for value in (state["runtime_sha256"], state["partition"], state["lake"], state["lean"],
            plan["status"], plan.get("baseline", ""),
            *(len(plan.get(name, [])) for name in ("recheck", "changed", "added", "removed"))):
        print(value)


def result_value(root: pathlib.Path, directory: pathlib.Path, report: pathlib.Path, built: bool) -> dict:
    from delta import baseline_identity, validate_report_sha
    from report_cache import member
    state = validate(root, directory)
    if state["needs_lean_build"] and not built:
        raise ValueError("prepared inspection has no successful Lean build evidence")
    # Publication has validated the full report; snapshots also require accepted
    # current transport. Bind those accepted bytes without replaying semantics.
    provenance = baseline_identity(report)
    report_sha = file_sha(report)
    validate_report_sha(report, report_sha)
    seed = read_json(member(report, ".seed.json"))
    if (provenance["input_address"] != "sha256:" + state["input_address"]
            or provenance["report_sha256"] != report_sha
            or seed.get("schema") != "lean-report-seed-v1"
            or seed.get("partition") != state["partition"]
            or seed.get("runtime_sha256") != state["runtime_sha256"]
            or seed.get("report_sha256") != report_sha
            or seed.get("materials_sha256") != file_sha(member(report, ".materials.zip"))):
        raise ValueError("accepted report does not match report preparation")
    return dict(schema=RESULT_SCHEMA, input_address=state["input_address"],
        runtime_sha256=state["runtime_sha256"], partition=state["partition"], report_sha256=report_sha,
        lean_build_executed=built, lean_build_succeeded=built)


def validate_result(root: pathlib.Path, directory: pathlib.Path, accepted_report: pathlib.Path) -> dict:
    result = read_json(directory / "result.json")
    if (set(result) != RESULT_FIELDS or type(result["lean_build_executed"]) is not bool
            or type(result["lean_build_succeeded"]) is not bool):
        raise ValueError("report preparation result is malformed")
    expected = result_value(root, directory, accepted_report, result["lean_build_executed"])
    if result != expected:
        raise ValueError("report preparation result does not match accepted production")
    return result


def complete(root: pathlib.Path, directory: pathlib.Path, report: pathlib.Path, execution: pathlib.Path) -> None:
    root, directory = root.resolve(), location(root.resolve(), directory)
    evidence = read_json(execution)
    if set(evidence) != {"lean_build_succeeded"} or type(evidence["lean_build_succeeded"]) is not bool:
        raise ValueError("producer execution evidence is malformed")
    write_json(directory / "result.json", result_value(root, directory, report, evidence["lean_build_succeeded"]))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("prepare", "resume", "complete"))
    parser.add_argument("--repository", required=True, type=pathlib.Path)
    parser.add_argument("--directory", required=True, type=pathlib.Path)
    parser.add_argument("--execution-plan", type=pathlib.Path)
    parser.add_argument("--report", type=pathlib.Path)
    parser.add_argument("--execution", type=pathlib.Path)
    args = parser.parse_args()
    try:
        root, directory = args.repository.resolve(), location(args.repository.resolve(), args.directory)
        if args.command == "complete":
            complete(root, directory, args.report, args.execution)
        else:
            (directory / "result.json").unlink(missing_ok=True)
            state = prepare(root, directory) if args.command == "prepare" else validate(root, directory)
            if args.execution_plan:
                execution_plan(directory, state, args.execution_plan)
            else:
                print(json.dumps({"needs_lean_build": state["needs_lean_build"]}))
        return 0
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        print(f"lean-report-preparation: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
