#!/usr/bin/env python3
"""Run the preregistered balanced baseline/final M3 probe once, without retries."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import re
import base64

from measure import execute, measure, process_ok, timed_argv

M3_PATH = "tools/lean-inspector/LeanInformationAudit/Tests/Seal/M3.lean"
IMPORT_PATH = "tools/lean-inspector/LeanInformationAudit/Tests/Seal/ImportCost.lean"
M3_SHA256 = "e88e5b9d86876809cbbf9e725fdad3e2c1f2a952aeadaa1d0f4b05b9aa878497"
BASELINE_SHA = "53ec407c9a42ebcbbc83c3cf46129dd5faf0e751"
FINAL_SHA = "2344decae77045d4d444b9d870fa2f0e67ff702e"
INSTALLED_SHA = "e30316c5024b209880cf1e47852596d2f3ac4bcc"
FINAL_CORE_SHA = "d86a54869d231cc1d358eaedd797842fec8919de"
EXPORT_BYTES = 171790
EXPORT_SHA256 = "e4aa9d1749672910a3479d734a6d89631a6a151f12d2b8a947c23bb6d81d70ee"
IDENTITY_SHA256 = "29247e3efa9866ba16a12555b175a60cdd3a483076800747890993e607192e87"
EXPECTED_AXIOMS = ["Classical.choice", "Quot.sound", "propext"]
DEPENDENCY_TARGETS = [
    "D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion",
    "D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative",
    "D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness",
    "D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog",
    "LeanInformationAudit.SealCommand",
]
SAMPLES = [("A1", "baseline"), ("B1", "final"), ("B2", "final"), ("A2", "baseline")]


IMPORT_SHA256 = "4c90fdd2a8e816f4a16a3e5c52f2083fe0e9e551c965890ef841e6c98c306c47"
PHASE_CAPS = {"warm": 1200, "imports": 120, "export": 300, "identities": 300, "module": 30}
PROBE_SECONDS = 11400  # 190 minutes, including preparation/cleanup/finalization
CLEANUP_SECONDS = 90
FINALIZE_SECONDS = 30
WORK_DEADLINE = None


def run(argv, cwd, env, output, name, timeout=300):
    output.mkdir(parents=True, exist_ok=True)
    out_path, time_path = output / f"{name}.stdout.log", output / f"{name}.time.txt"
    result, _, _ = execute(timed_argv(time_path, argv), cwd, env, timeout=timeout,
                           stdout=out_path, deadline=WORK_DEADLINE)
    result.update(argv=argv, stdout=str(out_path), time=str(time_path))
    return result


def git(root, *argv, check=True, env=None, timeout=10):
    result, data, _ = execute(["git", *argv], root, env or os.environ.copy(),
                              timeout=timeout, deadline=WORK_DEADLINE)
    code = result["exit"] if process_ok(result) else (result["exit"] or 1)
    completed = subprocess.CompletedProcess(argv, code, data.decode(), "")
    if check:
        completed.check_returncode()
    return completed


def bootstrap(root, head, output, revisions=None):
    """Fetch immutable inputs before the actual checkout API strips remotes."""
    global WORK_DEADLINE
    WORK_DEADLINE = time.monotonic() + 150
    revisions = revisions or (BASELINE_SHA, FINAL_SHA, INSTALLED_SHA, FINAL_CORE_SHA)
    env = os.environ.copy()
    token = env.pop("M3_READ_TOKEN", "")
    if token:
        index = int(env.get("GIT_CONFIG_COUNT", "0"))
        env[f"GIT_CONFIG_KEY_{index}"] = "http.https://github.com/.extraheader"
        credential = base64.b64encode(("x-access-token:" + token).encode()).decode()
        env[f"GIT_CONFIG_VALUE_{index}"] = "AUTHORIZATION: basic " + credential
        env["GIT_CONFIG_COUNT"] = str(index + 1)
    git(root, "fetch", "--no-tags", "--depth=1", "origin", *revisions, env=env, timeout=60)
    for revision in revisions:
        for kind in ("commit", "tree"):
            git(root, "cat-file", "-e", revision + "^{" + kind + "}")
    clean_env = os.environ.copy()
    clean_env.pop("M3_READ_TOKEN", None)
    result = run([sys.executable, str(root / "tools/scripts/workflow/ci.py"), "checkout",
                  "--repository", str(root), "--commit", head], root, clean_env, output,
                 "checkout", timeout=30)
    if not process_ok(result):
        raise RuntimeError("historical checkout/bootstrap failed")
    return {"verified_revisions": list(revisions), "checkout": result}


def direct_lean(tree, source, source_root=None):
    return [str(tree / "tools/scripts/worktree/lean-cache-run.sh"), "lake", "-d",
            "tools/lean-inspector", "env", "lean",
            "--root=" + str(source_root or tree / "tools/lean-inspector"), str(source)]


def import_result(result, text, label, source):
    source_matches = hashlib.sha256(source).hexdigest() == IMPORT_SHA256
    # The exact source pins the independent 143 limit. The baseline throws
    # before DTR_M3_IMPORTS, so a success-shaped diagnostic is not a failure.
    expected = "ImportCost: M3 closure changed: modules=144 interface=6"
    errors = [line for line in text.splitlines() if re.search(r"\berror:", line)]
    baseline = (label == "baseline" and process_ok(result, 1) and len(errors) == 1
                and errors[0].split("error:", 1)[1].strip() == expected
                and "DTR_M3_IMPORTS" not in text)
    final = (label == "final" and process_ok(result) and not errors
             and len(re.findall(r"(?m)^DTR_M3_IMPORTS modules=143 limit=143 interface=6$", text)) == 1)
    accepted = source_matches and (baseline or final)
    return {**result, "source_sha256": hashlib.sha256(source).hexdigest(),
            "source_matches": source_matches, "modules": (144 if baseline else 143) if accepted else None,
            "limit": 143 if source_matches else None, "interface": 6 if accepted else None,
            "expected_gate": "pass" if label == "final" else "known-baseline-limit-failure",
            "accepted": accepted}


def module_probe(tree, output, env, label):
    # Same relative filename as M3; the contents import only the pinned Lean
    # toolchain. Never execute the expensive original to validate --root.
    source_root = output / "module-probe" / label / "tools/lean-inspector"
    source = source_root / "LeanInformationAudit/Tests/Seal/M3.lean"
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_text("import Lean\nopen Lean Elab Command\nrun_cmd do\n"
                      "  let actual := (← getEnv).mainModule\n"
                      "  unless actual == `LeanInformationAudit.Tests.Seal.M3 do\n"
                      "    throwError \"wrong module: {actual}\"\n"
                      "  logInfo m!\"M3_MODULE_ID {actual}\"\n")
    result = run(direct_lean(tree, source, source_root), tree, env, output / "module",
                 label, timeout=PHASE_CAPS["module"])
    if not process_ok(result) or "M3_MODULE_ID LeanInformationAudit.Tests.Seal.M3" not in Path(result["stdout"]).read_text():
        raise RuntimeError(f"{label} direct Lean module identity failed")
    return result


def source_hash(root: Path, revision: str) -> str:
    data = git(root, "show", f"{revision}:{M3_PATH}").stdout.encode()
    return hashlib.sha256(data).hexdigest()


def normalized(path: Path) -> bytes:
    return json.dumps(json.loads(path.read_text()), sort_keys=True, separators=(",", ":")).encode()


def identity_summary(path: Path) -> dict:
    rows = json.loads(path.read_text())
    axioms = sorted({axiom for row in rows for axiom in row["axioms"]})
    return {
        "rows": len(rows),
        "sha256": hashlib.sha256(normalized(path)).hexdigest(),
        "axioms": axioms,
        "unexpected_axioms": sorted(set(axioms) - set(EXPECTED_AXIOMS)),
    }


def main():
    global WORK_DEADLINE
    parser = argparse.ArgumentParser()
    parser.add_argument("--repository", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--producer-dll", type=Path)
    parser.add_argument("--bootstrap", action="store_true")
    parser.add_argument("--head")
    args = parser.parse_args()
    root, output = args.repository.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    helper_dir = Path(__file__).resolve().parent
    plan = json.loads((helper_dir / "preregistered.json").read_text())
    (output / "preregistered.json").write_text(json.dumps(plan, indent=2) + "\n")
    if args.bootstrap:
        result = {"accepted": False}
        try:
            result.update(bootstrap(root, args.head, output / "bootstrap"), accepted=True)
        except Exception as exc:
            result["error"] = repr(exc)
        (output / "bootstrap.json").write_text(json.dumps(result, indent=2) + "\n")
        return 0 if result["accepted"] else 1
    if args.producer_dll is None:
        parser.error("--producer-dll required for measurement")
    started = time.monotonic()
    # CLOCK_MONOTONIC is shared by processes on this single host. The anchor
    # comes from the first job step, before checkout and setup.
    job_start = float(os.environ.get("M3_JOB_STARTED_MONOTONIC", started))
    final_deadline = min(started + PROBE_SECONDS, job_start + 231 * 60)
    WORK_DEADLINE = final_deadline - CLEANUP_SECONDS - FINALIZE_SECONDS
    summary = {
        "schema": "temporary-m3-hosted-probe-v2", "accepted": False,
        "plan": plan, "source_checks": {}, "warm": {}, "module_identity": {},
        "samples": {}, "imports": {}, "correspondence": {}, "cleanup": [],
        "runtime_budget": {"probe_seconds": PROBE_SECONDS, "job_work_stop_minutes": 231,
                           "cleanup_seconds": CLEANUP_SECONDS, "finalize_seconds": FINALIZE_SECONDS},
    }
    env = os.environ.copy()
    env.update(STRATALINT_LEAN_CACHE_RELEASE_TIMEOUT_SECONDS="5", GIT_OPTIONAL_LOCKS="0",
               STRATALINT_LEAN_PRODUCER_DLL=str(args.producer_dll.resolve()),
               STRATALINT_LEAN_CACHE_DONOR_REPOSITORY=str(root))
    trees, import_sources = {}, {}
    temp_root = Path(tempfile.mkdtemp(prefix="m3-probe-worktrees-"))
    # Useful incomplete results survive interruption before the last sample.
    def checkpoint():
        (output / "summary.json.tmp").write_text(json.dumps(summary, indent=2) + "\n")
        (output / "summary.json.tmp").replace(output / "summary.json")
    def require_time(seconds=0):
        if time.monotonic() + seconds > WORK_DEADLINE:
            raise RuntimeError("incomplete: remaining global budget cannot cover the remaining fixed plan")
    try:
        checkpoint()
        # 185 minutes of process ceilings + 120 seconds preparation. This is
        # admission to a bounded attempt, not evidence of runtime feasibility.
        require_time(11100 + 120)
        for label, revision in (("baseline", BASELINE_SHA), ("final", FINAL_SHA),
                                ("installed_integration", INSTALLED_SHA), ("final_core", FINAL_CORE_SHA)):
            actual = source_hash(root, revision)
            summary["source_checks"][label] = {"revision": revision, "sha256": actual, "matches": actual == M3_SHA256}
            if actual != M3_SHA256:
                raise RuntimeError(f"{label} M3 source hash mismatch")
        for label, revision in (("baseline", BASELINE_SHA), ("final", FINAL_SHA)):
            import_sources[label] = git(root, "show", f"{revision}:{IMPORT_PATH}").stdout.encode()
            if hashlib.sha256(import_sources[label]).hexdigest() != IMPORT_SHA256:
                raise RuntimeError(f"{label} original import threshold source changed")
            if git(root, "show", f"{revision}:lean-toolchain").stdout != (root / "lean-toolchain").read_text():
                raise RuntimeError("toolchain mismatch")
            tree = temp_root / label
            trees[label] = tree
            git(root, "worktree", "add", "--detach", str(tree), revision)
        checkpoint()
        for label, tree in trees.items():
            warm = run([str(tree / "tools/scripts/worktree/lean-cache-run.sh"), "--build",
                        *DEPENDENCY_TARGETS, "LeanInformationAudit.Tests.Seal.M3"],
                       tree, env, output / "warm", label, timeout=PHASE_CAPS["warm"])
            summary["warm"][label] = warm
            checkpoint()
            if not process_ok(warm):
                raise RuntimeError(f"{label} warm build failed or exceeded budget")
            summary["module_identity"][label] = module_probe(tree, output, env, label)
        for sample, label in SAMPLES:
            require_time()
            measured = measure(direct_lean(trees[label], M3_PATH), trees[label], env,
                               output / "samples", sample, deadline=WORK_DEADLINE)
            measured["variant"] = label
            summary["samples"][sample] = measured
            checkpoint()
        for label, tree in trees.items():
            require_time()
            result = run(direct_lean(tree, IMPORT_PATH), tree, env, output / "imports",
                         label, timeout=PHASE_CAPS["imports"])
            summary["imports"][label] = import_result(result, Path(result["stdout"]).read_text(),
                                                       label, import_sources[label])
            checkpoint()
        for label, tree in trees.items():
            require_time()
            directory = output / "correspondence"
            directory.mkdir(exist_ok=True)
            export_path = directory / f"{label}.analysis.json"
            identities_raw = directory / f"{label}.identities.raw.json"
            export = run(direct_lean(tree, helper_dir / "M3Export.lean", helper_dir), tree,
                         dict(env, M3_ANALYSIS_PATH=str(export_path)), directory,
                         f"{label}-export", timeout=PHASE_CAPS["export"])
            identity = run(direct_lean(tree, helper_dir / "OriginalIdentities.lean", helper_dir), tree,
                           dict(env, M3_IDENTITIES_PATH=str(identities_raw)), directory,
                           f"{label}-identities", timeout=PHASE_CAPS["identities"])
            summary["correspondence"][label] = {"export_process": export, "identity_process": identity}
            checkpoint()
            if not process_ok(export) or not process_ok(identity):
                raise RuntimeError(f"{label} correspondence process failed or exceeded budget")
            # A separate bounded normalizer process; included in the 120s
            # preparation/normalization allowance (2 calls of at most 10s).
            normalized_path = identities_raw.with_name(identities_raw.name.replace(".raw.json", ".json"))
            normalizer = run([sys.executable, str(helper_dir / "hash-identities.py"), str(identities_raw)],
                             root, env, directory, f"{label}-normalize", timeout=10)
            if not process_ok(normalizer):
                raise RuntimeError(f"{label} identity normalization failed")
            require_time()
            export_bytes = normalized(export_path)
            summary["correspondence"][label].update(
                export={"bytes": len(export_bytes), "sha256": hashlib.sha256(export_bytes).hexdigest()},
                identities=identity_summary(normalized_path), normalizer=normalizer)
            checkpoint()
        summary["samples_accepted"] = (len(summary["samples"]) == len(SAMPLES)
            and all(row["accepted"] and process_ok(row) for row in summary["samples"].values()))
        summary["imports_accepted"] = all(summary["imports"][label]["accepted"] for label in trees)
        summary["correspondence_accepted"] = all(
            row["export"]["bytes"] == EXPORT_BYTES and row["export"]["sha256"] == EXPORT_SHA256
            and row["identities"]["rows"] == 282 and row["identities"]["sha256"] == IDENTITY_SHA256
            and row["identities"]["axioms"] == EXPECTED_AXIOMS and not row["identities"]["unexpected_axioms"]
            for row in summary["correspondence"].values())
        summary["accepted"] = all(summary[key] for key in
                                   ("samples_accepted", "imports_accepted", "correspondence_accepted"))
    except Exception as exc:
        summary.update(error=repr(exc), accepted=False)
    finally:
        WORK_DEADLINE = min(time.monotonic() + CLEANUP_SECONDS, final_deadline - FINALIZE_SECONDS)
        for tree in trees.values():
            result = git(root, "worktree", "remove", "--force", str(tree), check=False, timeout=40)
            summary["cleanup"].append({"tree": str(tree), "exit": result.returncode})
            if result.returncode:
                summary.update(accepted=False, cleanup_incomplete=True)
        # No global worktree prune or deletion of other sessions' material.
        if temp_root.exists() and not any(temp_root.iterdir()):
            temp_root.rmdir()
        summary["wall_seconds"] = time.monotonic() - started
        summary["incomplete"] = not summary["accepted"]
        if time.monotonic() >= final_deadline:
            summary.update(accepted=False, incomplete=True, error="global finalization deadline exceeded")
        checkpoint()
        if time.monotonic() >= final_deadline and summary["accepted"]:
            summary.update(accepted=False, incomplete=True, error="global finalization deadline exceeded")
            checkpoint()
    print(json.dumps({"accepted": summary["accepted"], "incomplete": summary["incomplete"]}))
    return 0 if summary["accepted"] else 1


if __name__ == "__main__":
    sys.exit(main())
