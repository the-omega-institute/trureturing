#!/usr/bin/env python3
"""Run the preregistered balanced baseline/final M3 probe once, without retries."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import re

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


def timed_argv(path: Path, argv: list[str]) -> list[str]:
    flag = "-l" if sys.platform == "darwin" else "-v"
    return ["/usr/bin/time", flag, "-o", str(path), *argv]


def run(argv: list[str], cwd: Path, env: dict[str, str], output: Path, name: str, timeout: int = 1800) -> dict:
    output.mkdir(parents=True, exist_ok=True)
    out_path = output / f"{name}.stdout.log"
    time_path = output / f"{name}.time.txt"
    started = time.monotonic()
    output_bytes = 0
    output_truncated = False
    code = None
    error = None
    try:
        process = subprocess.Popen(
            timed_argv(time_path, argv),
            cwd=cwd,
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        with out_path.open("wb") as handle:
            def drain() -> None:
                nonlocal output_bytes, output_truncated
                assert process.stdout is not None
                for chunk in iter(lambda: process.stdout.read(65536), b""):
                    remaining = 16 * 1024 * 1024 - output_bytes
                    if remaining > 0:
                        handle.write(chunk[:remaining])
                        handle.flush()
                    output_bytes += len(chunk)
                    if output_bytes > 16 * 1024 * 1024:
                        output_truncated = True
            thread = threading.Thread(target=drain, daemon=True)
            thread.start()
            try:
                code = process.wait(timeout=timeout)
                error = None
            except subprocess.TimeoutExpired:
                code = None
                error = f"timeout>{timeout}s"
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    code = process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    code = process.wait()
            thread.join()
    except subprocess.TimeoutExpired as exc:
        code = None
        error = f"timeout>{timeout}s: {exc}"
    except OSError as exc:
        code = None
        error = repr(exc)
    return {
        "argv": argv,
        "cwd": str(cwd),
        "exit": code,
        "error": error,
        "wall_seconds": time.monotonic() - started,
        "max_seconds": timeout,
        "output_bytes": output_bytes,
        "output_limit_bytes": 16 * 1024 * 1024,
        "output_truncated": output_truncated,
        "stdout": str(out_path),
        "time": str(time_path),
    }


def git(root: Path, *argv: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(["git", *argv], cwd=root, text=True, check=check, capture_output=True)


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


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repository", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--producer-dll", required=True, type=Path)
    args = parser.parse_args()
    root = args.repository.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    summary: dict = {
        "schema": "temporary-m3-hosted-probe-v1",
        "plan": {"samples": [name for name, _ in SAMPLES], "order": SAMPLES, "retries": 0},
        "source": {"path": M3_PATH, "expected_sha256": M3_SHA256, "baseline": BASELINE_SHA, "final": FINAL_SHA},
        "expected_correspondence": {
            "export_bytes": EXPORT_BYTES,
            "export_sha256": EXPORT_SHA256,
            "declarations": 282,
            "identity_sha256": IDENTITY_SHA256,
            "axioms": EXPECTED_AXIOMS,
        },
        "source_checks": {},
        "warm": {},
        "samples": {},
        "imports": {},
        "correspondence": {},
    }
    env = os.environ.copy()
    env.update({
        "STRATALINT_LEAN_CACHE_RELEASE_TIMEOUT_SECONDS": "5",
        "GIT_OPTIONAL_LOCKS": "0",
        "STRATALINT_LEAN_PRODUCER_DLL": str(args.producer_dll.resolve()),
        "STRATALINT_LEAN_CACHE_DONOR_REPOSITORY": str(root),
    })
    wrapper = lambda tree: str(tree / "tools/scripts/worktree/lean-cache-run.sh")
    helper_dir = Path(__file__).resolve().parent
    (output / "helpers").mkdir(parents=True, exist_ok=True)
    for helper in ("M3Export.lean", "OriginalIdentities.lean"):
        shutil.copy2(helper_dir / helper, output / "helpers" / helper)
    trees: dict[str, Path] = {}
    try:
        for label, revision in (("baseline", BASELINE_SHA), ("final", FINAL_SHA),
                                ("installed_integration", INSTALLED_SHA), ("final_core", FINAL_CORE_SHA)):
            actual = source_hash(root, revision)
            summary["source_checks"][label] = {"revision": revision, "sha256": actual, "matches": actual == M3_SHA256}
            if actual != M3_SHA256:
                raise RuntimeError(f"{label} M3 source hash mismatch: {actual}")
        with tempfile.TemporaryDirectory(prefix="m3-probe-worktrees-") as temp:
            temp_root = Path(temp)
            for label, revision in (("baseline", BASELINE_SHA), ("final", FINAL_SHA)):
                tree = temp_root / label
                git(root, "worktree", "add", "--detach", str(tree), revision)
                trees[label] = tree
            for label, tree in trees.items():
                warm = run(
                    [wrapper(tree), "--build", *DEPENDENCY_TARGETS, "LeanInformationAudit.Tests.Seal.M3"],
                    tree,
                    env,
                    output / "warm",
                    label,
                )
                summary["warm"][label] = {"targets": DEPENDENCY_TARGETS + ["LeanInformationAudit.Tests.Seal.M3"], **warm}
                if warm["exit"] != 0:
                    raise RuntimeError(f"{label} warm build failed")
            for sample, label in SAMPLES:
                tree = trees[label]
                command = [wrapper(tree), "lake", "-d", "tools/lean-inspector", "env", "lean", M3_PATH]
                sample_dir = output / "samples"
                result = subprocess.run(
                    [sys.executable, str(helper_dir / "measure.py"), "--output", str(sample_dir),
                     "--sample", sample, "--cwd", str(tree), "--", *command],
                    cwd=root, env=env, text=True, capture_output=True, check=False,
                )
                (output / f"{sample}.driver.stdout.log").write_text(result.stdout)
                (output / f"{sample}.driver.stderr.log").write_text(result.stderr)
                result_path = sample_dir / f"{sample}.result.json"
                measured = json.loads(result_path.read_text()) if result_path.exists() else {
                    "accepted": False, "exit": result.returncode, "driver_error": result.stdout[-4000:],
                }
                measured["variant"] = label
                summary["samples"][sample] = measured
            for label, tree in trees.items():
                imports = run(
                    [wrapper(tree), "lake", "-d", "tools/lean-inspector", "env", "lean", IMPORT_PATH],
                    tree,
                    env,
                    output / "imports",
                    label,
                )
                import_log = Path(imports["stdout"])
                import_text = import_log.read_text(errors="replace") if import_log.exists() else ""
                match = re.search(r"modules=(\d+) limit=(\d+) interface=(\d+)", import_text)
                summary["imports"][label] = {
                    **imports,
                    "modules": int(match.group(1)) if match else None,
                    "limit": int(match.group(2)) if match else None,
                    "interface": int(match.group(3)) if match else None,
                    "expected_gate": "pass" if label == "final" else "known-baseline-limit-failure",
                }
            for label, tree in trees.items():
                export_path = output / "correspondence" / f"{label}.analysis.json"
                identities_raw = output / "correspondence" / f"{label}.identities.raw.json"
                export_path.parent.mkdir(parents=True, exist_ok=True)
                export_env = dict(env, M3_ANALYSIS_PATH=str(export_path))
                export = run(
                    [wrapper(tree), "lake", "-d", "tools/lean-inspector", "env", "lean", str(output / "helpers" / "M3Export.lean")],
                    tree,
                    export_env,
                    output / "correspondence",
                    f"{label}-export",
                )
                identity_env = dict(env, M3_IDENTITIES_PATH=str(identities_raw))
                identity = run(
                    [wrapper(tree), "lake", "-d", "tools/lean-inspector", "env", "lean", str(output / "helpers" / "OriginalIdentities.lean")],
                    tree,
                    identity_env,
                    output / "correspondence",
                    f"{label}-identities",
                )
                if export["exit"] != 0 or identity["exit"] != 0:
                    raise RuntimeError(f"{label} correspondence process failed")
                identity_digest = subprocess.run(
                    [sys.executable, str(helper_dir / "hash-identities.py"), str(identities_raw)],
                    cwd=root, text=True, capture_output=True, check=False,
                )
                normalized_identities = identities_raw.with_name(
                    identities_raw.name.replace(".raw.json", ".json")
                )
                if identity_digest.returncode != 0 or not normalized_identities.exists():
                    raise RuntimeError(f"{label} identity normalization failed")
                export_bytes = normalized(export_path)
                identity_summary_value = identity_summary(normalized_identities)
                summary["correspondence"][label] = {
                    "export": {"bytes": len(export_bytes), "sha256": hashlib.sha256(export_bytes).hexdigest(), "path": str(export_path)},
                    "identities": {**identity_summary_value, "raw_path": str(identities_raw), "path": str(normalized_identities)},
                    "export_process": export,
                    "identity_process": identity,
                    "identity_normalizer": {"exit": identity_digest.returncode, "stdout": identity_digest.stdout},
                }
            base = summary["correspondence"]["baseline"]
            final = summary["correspondence"]["final"]
            summary["correspondence"]["equal"] = {
                "export": base["export"]["sha256"] == final["export"]["sha256"],
                "identities": base["identities"]["sha256"] == final["identities"]["sha256"],
            }
    except Exception as error:
        summary["error"] = repr(error)
    finally:
        for tree in trees.values():
            git(root, "worktree", "remove", "--force", str(tree), check=False)
        git(root, "worktree", "prune", check=False)
        summary["samples_accepted"] = all(row.get("accepted", False) for row in summary["samples"].values()) and len(summary["samples"]) == len(SAMPLES)
        baseline_imports = summary["imports"].get("baseline", {})
        final_imports = summary["imports"].get("final", {})
        summary["imports_accepted"] = (
            baseline_imports.get("modules") == 144 and baseline_imports.get("limit") == 143
            and baseline_imports.get("interface") == 6 and baseline_imports.get("exit") != 0
            and final_imports.get("modules") == 143 and final_imports.get("limit") == 143
            and final_imports.get("interface") == 6 and final_imports.get("exit") == 0
        )
        summary["correspondence_accepted"] = False
        if "baseline" in summary["correspondence"] and "final" in summary["correspondence"]:
            rows = [summary["correspondence"][x] for x in ("baseline", "final")]
            summary["correspondence_accepted"] = all(
                row["export"]["bytes"] == EXPORT_BYTES and row["export"]["sha256"] == EXPORT_SHA256
                and row["identities"]["rows"] == 282 and row["identities"]["sha256"] == IDENTITY_SHA256
                and row["identities"]["axioms"] == EXPECTED_AXIOMS and not row["identities"]["unexpected_axioms"]
                for row in rows
            ) and summary["correspondence"].get("equal", {}).get("export") and summary["correspondence"].get("equal", {}).get("identities")
        summary["accepted"] = summary["samples_accepted"] and summary["imports_accepted"] and summary["correspondence_accepted"] and "error" not in summary
        (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({"accepted": summary["accepted"], "samples_accepted": summary["samples_accepted"], "correspondence_accepted": summary["correspondence_accepted"]}, separators=(",", ":")))
    return 0 if summary["accepted"] else 1


if __name__ == "__main__":
    sys.exit(main())
