"""Select and check affected downstream Omega consumers using the frozen adapter."""

import argparse
from collections import defaultdict
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools/scripts/workflow"))
from ci_detect import read_changed

CONSUMER_ROOTS = {"D5", "Reg", "Trureturing"}
SHARED = {"lean-toolchain", "lakefile.toml", "lake-manifest.json", "Makefile",
          "Meta/ci-units.json", "Meta/tools-release.json", ".github/workflows/ci-current.yml",
          ".github/scripts/omega-consumer.py", ".github/scripts/test-omega-consumer.py",
          ".github/scripts/omega-audit-results.py", ".github/scripts/test-omega-audit-results.py"}
REG_INPUTS = {"Reg/lakefile.toml", "Reg/lake-manifest.json"}
RELEASE_INPUTS = {"lean-toolchain", "lakefile.toml", "lake-manifest.json", "Makefile",
                  "Meta/omegamath-release.json", ".github/scripts/verify-omegamath-release.py",
                  ".github/scripts/test-verify-omegamath-release.py"} | REG_INPUTS
REPORT = ".lake/build/omega-checks/selected-official-axioms.json"


def namespace(name):
    return name.partition(".")[0]


def downstream_module(path):
    if path == "Trureturing.lean" or path.startswith(("D5/", "Reg/")) and path.endswith(".lean"):
        return path.removesuffix(".lean").replace("/", ".")
    return None


def shared_change(paths):
    return bool(SHARED.intersection(paths)) or any(
        path.startswith("src/OmegaChecks/") and path.endswith(".py") for path in paths)


def select(graph, consumers, paths):
    eligible = {name for name in consumers if namespace(name) in CONSUMER_ROOTS}
    if paths is None:
        return sorted(eligible)
    paths = set(paths)
    changed = {name for path in paths if (name := downstream_module(path))}
    reverse = defaultdict(set)
    for name, imports in graph.items():
        for dependency in imports:
            reverse[dependency].add(name)
    missing = {name for name in changed - graph.keys() if reverse[name]}
    if missing:
        raise ValueError(f"removed consumer inputs still imported: {sorted(missing)}")
    if shared_change(paths):
        return sorted(eligible)
    if paths & REG_INPUTS:
        changed.update(name for name in graph if namespace(name) in {"Reg", "LeanInformationAuditInterface"})
    affected = set(changed)
    pending = list(affected)
    while pending:
        for importer in reverse[pending.pop()] - affected:
            affected.add(importer)
            pending.append(importer)
    return sorted(eligible & affected)


def portable_adapter():
    # Lake resolves the pinned dependency before the adapter reads package sources.
    lean = subprocess.check_output(["lake", "env", "printenv", "LEAN"], cwd=ROOT, text=True).strip()
    sys.path.insert(0, str(ROOT / "src/OmegaChecks"))
    import portable
    return portable, lean


def discover(changed):
    paths = read_changed(changed) if changed is not None else None
    if changed is not None and paths is None:
        raise ValueError(f"missing changed-path manifest: {changed}")
    scope = {"consumers": [], "verify_release": paths is None or bool(RELEASE_INPUTS.intersection(paths))}
    if paths is not None and not (shared_change(paths) or REG_INPUTS.intersection(paths)
                                  or any(downstream_module(path) for path in paths)):
        return scope, None, None
    adapter, lean = portable_adapter()
    sources, graph = adapter.import_graph(lean, with_reg=True)
    scope["consumers"] = select(graph, adapter.consumers(graph), paths)
    return scope, adapter, (sources, graph)


def load_scope(path):
    scope = json.loads(path.read_text())
    if (not isinstance(scope, dict) or set(scope) != {"consumers", "verify_release"}
            or type(scope["verify_release"]) is not bool):
        raise ValueError(f"invalid downstream consumer scope: {path}")
    names = scope["consumers"]
    if (not isinstance(names, list) or not all(isinstance(name, str) and namespace(name) in CONSUMER_ROOTS
                                               for name in names) or names != sorted(set(names))):
        raise ValueError(f"invalid downstream consumer scope: {path}")
    return scope


def check(names, adapter, discovered=None):
    if names:
        # Explicit scoped mode leaves the upstream qualification suite to the release producer.
        adapter.check(names, "both", basis_roots=[], common_roots=(), discovered=discovered)
    else:
        print("No affected downstream Omega consumers", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--changed", type=Path, default=os.environ.get("CI_CHANGED_PATHS_FILE"))
    parser.add_argument("--scope", type=Path, default=os.environ.get("OMEGA_SCOPE_FILE"))
    parser.add_argument("--write-scope", type=Path)
    parser.add_argument("--cache-targets", type=Path)
    args = parser.parse_args()
    if args.write_scope:
        if not args.changed or not args.cache_targets or args.scope:
            parser.error("--write-scope requires --changed and --cache-targets")
        scope, _, _ = discover(args.changed)
        names = scope["consumers"]
        args.write_scope.write_text(json.dumps(scope) + "\n")
        args.cache_targets.write_text("".join(name + "\n" for name in names))
        if names and (output := os.environ.get("GITHUB_OUTPUT")):
            with open(output, "a") as stream:
                print(f"targets-file={args.cache_targets}", file=stream)
                print(f"report-file={REPORT}", file=stream)
        print(f"Downstream Omega scope: {len(names)} consumers", flush=True)
    else:
        if args.scope:
            scope = load_scope(args.scope)
            adapter = discovered = None
        else:
            scope, adapter, discovered = discover(args.changed)
        if scope["verify_release"]:
            subprocess.run(["make", "verify-omegamath-release"], cwd=ROOT, check=True)
        if scope["consumers"] and adapter is None:
            adapter, _ = portable_adapter()
        check(scope["consumers"], adapter, discovered)


if __name__ == "__main__":
    main()
