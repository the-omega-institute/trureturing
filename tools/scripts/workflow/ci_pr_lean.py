"""Build and check the selected Lean and Scribe inputs of a CI candidate."""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

from ci_contract import read_changed, write_paths

SCRIBE = ["dotnet", "tools/StrataLint.Scribe/bin/Release/net10.0/StrataLint.Scribe.dll"]
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


def report_batches(scope, limit=60_000):
    # Each root list is passed through make, Lake and dotnet as one argv string.
    # Keep every document with all its truth anchors when a large diff needs batches.
    all_targets = scope["targets"]
    if not all_targets:
        return
    if sum(len(name) + 1 for name in all_targets) <= limit:
        yield all_targets, scope["paths"]
        return
    definitions = scope["definitions"]
    document_targets = {name for roots in definitions.values() for name in roots}
    groups = [(refs, path) for path, refs in sorted(definitions.items())]
    groups.extend(([name], None) for name in all_targets if name not in document_targets)
    targets, documents, size = set(), [], 0
    for names, document in groups:
        added = set(names) - targets
        extra = sum(len(name) + 1 for name in added)
        if targets and size + extra > limit:
            yield sorted(targets), documents
            targets, documents, size = set(), [], 0
            extra = sum(len(name) + 1 for name in set(names))
        targets.update(names)
        size += extra
        if document is not None:
            documents.append(document)
    if targets:
        yield sorted(targets), documents


def check(paths):
    with tempfile.TemporaryDirectory(prefix="ci-pr-lean-") as temporary:
        directory = Path(temporary)
        manifest = directory / "paths"
        write_paths(manifest, paths)
        plan = subprocess.run([*SCRIBE, "lean-inputs", "--affected", "--paths-from", str(manifest)],
                              stdout=subprocess.PIPE, text=True, check=True)
        scope = json.loads(plan.stdout)
        programs, targets = scope["programs"], scope["targets"]
        if any(not MODULE.fullmatch(module) for module in [*targets, *programs]):
            raise ValueError("invalid Lean module in CI scope")
        print(f"CI_SCOPED_LEAN report_targets={len(targets)} program_targets={len(programs)}", flush=True)
        environment = dict(os.environ, STRATALINT_ACCEPT_COLD_BUILD="1")
        if programs:
            subprocess.run(["bash", "tools/scripts/worktree/lean-cache-run.sh", "lake",
                            "-d", "tools/lean-inspector-reg", "build",
                            *["+" + module for module in programs]], env=environment, check=True)
        for targets, selected_paths in report_batches(scope):
            report = directory / "scoped-lean-report.json"
            subprocess.run(["make", "lean-report-scoped", "LEAN_TARGETS=" + " ".join(targets)],
                           env=dict(environment, LEAN_REPORT=str(report), LEAN_NUM_THREADS="1"), check=True)
            roots = directory / "roots"
            write_paths(roots, [name.replace(".", "/") + ".lean" for name in targets])
            write_paths(manifest, selected_paths)
            subprocess.run([*SCRIBE, "content-check", "--scoped", "--report", str(report),
                            "--targets-from", str(roots), "--paths-from", str(manifest)], check=True)
    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    try:
        paths = read_changed(parser.parse_args().manifest)
        if paths is None:
            raise ValueError("missing scoped Lean path manifest")
        sys.exit(check(paths))
    except subprocess.CalledProcessError as error:
        sys.exit(error.returncode if error.returncode > 0 else 128 - error.returncode)
    except (OSError, ValueError, KeyError) as error:
        print("CI_SCOPED_LEAN_ERROR " + str(error), file=sys.stderr)
        sys.exit(2)
