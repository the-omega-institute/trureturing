"""Build scoped Lean evidence and check the candidate and its selected delta."""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

from ci_contract import read_changed, write_paths
from ci_checks import CLI

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


def check(manifest, protected_base=None):
    if read_changed(manifest) is None:
        raise ValueError("missing changed-path manifest")
    with tempfile.TemporaryDirectory(prefix="ci-pr-lean-") as temporary:
        directory = Path(temporary)
        plan = subprocess.run([*SCRIBE, "lean-inputs", "--affected", "--paths-from", str(manifest)],
                              stdout=subprocess.PIPE, text=True, check=True)
        scope = json.loads(plan.stdout)
        programs, targets = scope["programs"], scope["targets"]
        if any(not MODULE.fullmatch(module) for module in [*targets, *programs]):
            raise ValueError("invalid Lean module in PR scope")
        print(f"CI_PR_LEAN report_targets={len(targets)} program_targets={len(programs)}", flush=True)
        environment = dict(os.environ, STRATALINT_ACCEPT_COLD_BUILD="1")
        if programs:
            subprocess.run(["bash", "tools/scripts/worktree/lean-cache-run.sh", "lake",
                            "-d", "tools/lean-inspector-reg", "build",
                            *["+" + module for module in programs]], env=environment, check=True)
        reports = []
        for index, (targets, selected_paths) in enumerate(report_batches(scope)):
            batch = directory / str(index)
            batch.mkdir()
            report = batch / "scoped-lean-report.json"
            subprocess.run(["make", "lean-report-scoped", "LEAN_TARGETS=" + " ".join(targets)],
                           env=dict(environment, LEAN_REPORT=str(report), LEAN_NUM_THREADS="1"), check=True)
            reports.append(str(report))
            roots = batch / "roots"
            documents = batch / "documents"
            write_paths(roots, [name.replace(".", "/") + ".lean" for name in targets])
            write_paths(documents, selected_paths)
            subprocess.run([*SCRIBE, "content-check", "--scoped", "--report", str(report),
                            "--targets-from", str(roots), "--paths-from", str(documents)], check=True)

        report_list = directory / "reports"
        write_paths(report_list, reports)
        arguments = ["--changed-paths-from", str(manifest), "--scoped-reports-from", str(report_list)]
        current = subprocess.run(["dotnet", CLI, "check-current", *arguments])
        if protected_base is None:
            return current.returncode
        delta = subprocess.run(["dotnet", CLI, "check-delta", "--protected-base", protected_base, *arguments])
        return current.returncode or (0 if delta.returncode == 3 else delta.returncode)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--protected-base")
    args = parser.parse_args()
    try:
        code = check(args.manifest, args.protected_base)
        sys.exit(code if code >= 0 else 128 - code)
    except subprocess.CalledProcessError as error:
        sys.exit(error.returncode if error.returncode > 0 else 128 - error.returncode)
    except (OSError, ValueError, KeyError) as error:
        print("CI_PR_LEAN_ERROR " + str(error), file=sys.stderr)
        sys.exit(2)
