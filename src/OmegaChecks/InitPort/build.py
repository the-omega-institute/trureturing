"""Generate independent, audited kernel modules from the installed Lean Init."""
import argparse
from collections import Counter, defaultdict
from graphlib import CycleError, TopologicalSorter
import json
import omegamath
from pathlib import Path
from report import report
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
DEFAULT_SEED = ROOT / ".lake/build/omega-strict/lib/lean"


def run(*args, **options):
    subprocess.run(args, cwd=ROOT, check=True, **options)


def all_modules():
    prefix = subprocess.check_output(["lean", "--print-prefix"], cwd=ROOT, text=True).strip()
    lib = Path(prefix) / "lib" / "lean"
    return ["Init", *sorted(".".join(p.relative_to(lib).with_suffix("").parts)
                            for p in (lib / "Init").rglob("*.olean"))]


def snapshot_seed(installed, seed):
    files = [*installed.glob("OmegaInit.*"), *(installed / "OmegaInit").rglob("*")]
    for file in files:
        if file.is_file() and file.name.endswith((".olean", ".olean.server", ".olean.private", ".ir", ".ir.sig")):
            dest = seed / file.relative_to(installed)
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(file, dest)


def cyclic_declarations(path):
    graph = {}
    candidates = defaultdict(set)
    with path.open() as stream:
        for owner, name, dependencies in map(json.loads, stream):
            deps = json.loads(dependencies)
            if not name:
                graph[owner] = set(deps)
            else:
                for dep in deps:
                    candidates[owner, dep].add(name)
    list(TopologicalSorter(graph).static_order())
    rejected = {}
    for (owner, dep), names in sorted(candidates.items(), key=lambda row: (-len(row[1]), row[0])):
        pending = [dep]
        seen = set()
        while pending and owner not in seen:
            node = pending.pop()
            if node not in seen:
                seen.add(node)
                pending.extend(graph.get(node, set()) - seen)
        if owner in seen:
            rejected.update((n, f"cyclic module dependency from {owner} to {dep}") for n in names)
        else:
            graph[owner].add(dep)
    return rejected


def generate(stage, product, seed, roots, excluded):
    transfer = stage / "transfer"
    artifact = product / "lib"
    inventory = product / "inventory.jsonl"
    omissions = dict.fromkeys(excluded, "explicit exclusion")
    selection = product / "interface-rejections.jsonl"
    run("lake", "build", "omegaAudit", "+OmegaChecks.Interface.Equations", "+OmegaChecks.InitCompiler.Proofs",
        "+OmegaChecks.InitPort.Alternatives")
    with selection.open("w") as rejected:
        while True:
            exclusions = stage / "exclusions.json"
            exclusions.write_text(json.dumps(sorted(omissions.items())))
            run("lake", "env", "lean", "--run", HERE / "Kernel.lean", seed, transfer, inventory, exclusions, *roots)
            run("lean", "--run", HERE / "Modules.lean", transfer, seed, artifact, *roots)
            graph = dict(json.loads((product / "modules.json").read_text()))
            try:
                closure = list(TopologicalSorter(graph).static_order())
            except CycleError:
                new = cyclic_declarations(stage / "candidate-edges.jsonl")
            else:
                results = stage / "selection.jsonl"
                run("lake", "env", "lean", "--run", HERE / "Select.lean", artifact, seed, transfer, results, *graph)
                with results.open() as stream:
                    new = dict(map(json.loads, stream))
                if not new:
                    break
            if not new.keys() - omissions.keys():
                raise ValueError(f"no progress resolving {len(new)} rejected declarations")
            for name, why in sorted(new.items()):
                if name not in omissions:
                    print(json.dumps([name, why]), file=rejected)
            omissions.update(new)
            rejected.flush()
    run("lake", "env", "lean", "--run", HERE / "DuplicateSites.lean", product)
    graph = dict(json.loads((product / "modules.json").read_text()))
    closure = list(TopologicalSorter(graph).static_order())
    run("lean", "--run", HERE / "ExportAxioms.lean", artifact, *graph)
    with (product / "audit.txt").open("w") as log:
        audit = ROOT / ".lake/build/bin/omegaAudit"
        checked = subprocess.run(["lake", "env", audit, "--exact-roots", artifact, *graph, "--", *closure],
                                 cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=False)
    print((product / "audit.txt").read_text(), end="", flush=True)
    checked.check_returncode()
    with inventory.open() as stream:
        counts = Counter(row[3] for row in map(json.loads, stream))
    print(f"{counts['added']} translated declarations; {counts['existing']} source seed declarations")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="new directory for the audited module tree and inventory")
    parser.add_argument("modules", nargs="*", help="official Init roots (default: every installed Init module)")
    parser.add_argument("--seed", type=Path, default=DEFAULT_SEED, help="compiled strict OmegaInit seed")
    parser.add_argument("--exclude", action="append", default=[],
                        help="omit a generated candidate; declarations already in the seed cannot be excluded")
    parser.add_argument("--require-complete", action="store_true",
                        help="require checked implementations or impossibility evidence at all official sites")
    parser.add_argument("-j", type=int, default=4, help="parallel jobs for the full OmegaMath consumer build")
    args = parser.parse_args()
    seed = args.seed.resolve()
    target = args.output.resolve()
    if args.j < 1:
        parser.error("the job count must be positive")
    if args.require_complete and args.modules:
        parser.error("--require-complete must scan the entire pinned Init")
    if target.exists():
        parser.error(f"output directory already exists: {target}")
    if any(name != "Init" and not name.startswith("Init.") for name in args.modules):
        parser.error("module roots must belong to Init")
    if not (seed / "OmegaInit.olean.private").is_file():
        parser.error(f"compiled strict OmegaInit seed missing at {seed}")
    roots = args.modules or all_modules()
    target.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=target.parent, prefix=".init-port-") as work:
        stage = Path(work)
        snapshot_seed(seed, stage / "seed")
        product = stage / "product"
        product.mkdir()
        generate(stage, product, stage / "seed", roots, args.exclude)
        if not args.modules:
            report(product, require_complete=args.require_complete)
            omegamath.build(product, product / "lib", args.j, product / "omegamath-audit.txt")
        product.rename(target)


if __name__ == "__main__":
    main()
