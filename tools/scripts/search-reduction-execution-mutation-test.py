#!/usr/bin/env python3
"""Temporarily mutate execution boundaries and require named Lean test failures."""
from pathlib import Path
import os
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
ANALYSIS = ROOT / "tools/lean-inspector/LeanInformationAuditRegAnalysis/SearchReduction"
TARGET = "LeanInformationAuditRegTests.SearchReduction.ExecutionChainTests"
MUTATIONS = [
    ("kappa-early-stop", "Lookup.lean",
     "if trace.source?.isSome then break",
     "if trace.source?.isSome || result.searchKappa then break", "DPRIME_KAPPA"),
    ("G-as-exhaustive", "Lookup.lean",
     "trace := {trace with\n        complete := false, coveragePrefixG := true,",
     "trace := {trace with\n        complete := true, coveragePrefixG := false,", "DPRIME_G"),
    ("budget-miss-completes-guard", "Local.lean",
     "let toRun (result : LocalResult) := result.query.guardRun",
     "let toRun (result : LocalResult) :=\n        if result.query.price == some 1 then Run.exhausted else result.query.guardRun",
     "DPRIME_REVERSE"),
    ("publication-ignores-guard", "Commands.lean",
     "let reading := kernelGraphReading (r.graph?.getD {})",
     "let reading := { (kernelGraphReading (r.graph?.getD {})) with targetPartComplete := true }",
     "DPRIME_REVERSE"),
]


def build():
    env = dict(os.environ, SEARCH_REDUCTION_MEMO="0", SEARCH_REDUCTION_PROBE_CACHE="0",
               SEARCH_REDUCTION_RESUME="", SEARCH_REDUCTION_WORKERS="1")
    result = subprocess.run(["make", "lean", "LEAN_TARGETS=" + TARGET], cwd=ROOT,
                            env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    print(result.stdout, end="", flush=True)
    return result


def main():
    paths = sorted({ANALYSIS / mutation[1] for mutation in MUTATIONS})
    subprocess.run(["git", "diff", "--quiet", "HEAD", "--", *map(str, paths)],
                   cwd=ROOT, check=True)
    originals = {path: path.read_bytes() for path in paths}
    try:
        for name, filename, old, new, killed_by in MUTATIONS:
            path = ANALYSIS / filename
            text = originals[path].decode()
            if text.count(old) != 1:
                raise RuntimeError(f"{name}: mutation location is not unique")
            try:
                path.write_text(text.replace(old, new))
                result = build()
            finally:
                path.write_bytes(originals[path])
            if result.returncode == 0 or not re.search(
                    r"^error: .*" + killed_by, result.stdout, re.MULTILINE):
                raise RuntimeError(f"{name}: missing named test rejection {killed_by}")
            print(f"DPRIME_MUTATION {name} killed_by={killed_by} exit={result.returncode}", flush=True)
    finally:
        for path, content in originals.items():
            if path.read_bytes() != content:
                path.write_bytes(content)
    if build().returncode:
        raise RuntimeError("restored source failed its build")
    print("DPRIME_MUTATIONS_DONE killed=4 source=restored restored_build=passed", flush=True)


if __name__ == "__main__":
    main()
