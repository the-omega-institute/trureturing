"""Generate independent, audited kernel modules from the installed Lean Init."""
import argparse
from collections import Counter, defaultdict
from graphlib import CycleError, TopologicalSorter
import json
import omegamath
import os
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
    official_imports = {}
    candidates = defaultdict(set)
    with path.open() as stream:
        for owner, name, dependencies, *original in map(json.loads, stream):
            deps = json.loads(dependencies)
            if not name:
                graph[owner] = set(deps)
                official_imports[owner] = json.loads(original[0])
            else:
                for dep in deps:
                    candidates[owner, dep].add(name)
    list(TopologicalSorter(graph).static_order())
    ancestors = {}
    for owner in TopologicalSorter(official_imports).static_order():
        ancestors[owner] = set(official_imports.get(owner, []))
        for dep in official_imports.get(owner, []):
            ancestors[owner].update(ancestors[dep])

    # A late convenience proof can introduce the reverse of a physical Init
    # dependency. Keep the upstream direction before comparing candidate counts.
    def priority(item):
        (owner, dep), names = item
        return (owner in ancestors[dep], dep not in ancestors[owner], -len(names), owner, dep)

    rejected = {}
    for (owner, dep), names in sorted(candidates.items(), key=priority):
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
    order = TopologicalSorter({key: sorted(deps) for key, deps in sorted(graph.items())})
    return rejected, list(order.static_order())


def compile_tasks(stage, product, artifact, inventory, raw):
    bridge = stage / "task.c"
    run("lake", "env", "lean", "--run", HERE / "TaskNative.lean", artifact, raw, bridge)
    if not bridge.exists():
        return
    native = product / "native"
    native.mkdir(exist_ok=True)
    obj = native / "task.o"
    run("leanc", "-DLEAN_EXPORTING", "-c", bridge, "-o", obj)
    with inventory.open() as stream:
        installed = {name for mod, name, _, status, _ in map(json.loads, stream)
                     if mod == "Init.Core" and status in {"added", "existing"}}
    required = {"Task.spawn", "Task.map", "Task.bind", "Task.get", "Task.pure",
                "Task.Priority.default", "Task.Priority.max", "Task.Priority.dedicated"}
    if required <= installed:
        consumer = stage / "task-consumer.c"
        run("lean", "-R", HERE, "-c", consumer, HERE / "TaskConsumer.lean",
            env={**os.environ, "LEAN_PATH": str(artifact)})
        app = stage / "task-consumer"
        run("leanc", consumer, obj, HERE / "task_consumer.c", "-o", app)
        run(app)


def compile_state_runtime(stage, product, artifact, inventory, tool, filename, required, extra_sources=()):
    bridge = stage / (filename + ".c")
    run("lake", "env", "lean", "--run", HERE / (tool + "Native.lean"), artifact, bridge)
    if not bridge.exists():
        return
    native = product / "native"
    native.mkdir(exist_ok=True)
    if tool == "Promise":
        pinned = stage / "promise-result-d.c"
        run("lean", "-R", HERE, "-c", pinned, HERE / "PromiseResultD.lean")
        pinned_object = native / "promise-result-d.o"
        run("leanc", "-DLEAN_EXPORTING", "-I", stage, "-c", HERE / "promise_result_d.c", "-o", pinned_object)
        extra_sources = [*extra_sources, pinned_object]
    obj = native / (filename + ".o")
    run("leanc", "-DLEAN_EXPORTING", "-c", bridge, "-o", obj)
    with inventory.open() as stream:
        installed = {(mod, name) for mod, name, _, status, _ in map(json.loads, stream)
                     if status in {"added", "existing"}}
    if all((mod, name) in installed for mod, names in required.items() for name in names):
        consumer = stage / (filename + "-consumer.c")
        run("lean", "-R", HERE, "-c", consumer, HERE / (tool + "Consumer.lean"),
            env={**os.environ, "LEAN_PATH": str(artifact)})
        app = stage / (filename + "-consumer")
        run("leanc", consumer, obj, *extra_sources, HERE / (filename + "_consumer.c"), "-o", app)
        run(app)


def compile_type_name(stage, product, artifact, inventory):
    bridge = stage / "type-name.c"
    run("lake", "env", "lean", "--run", HERE / "TypeNameNative.lean", artifact, bridge)
    if not bridge.exists():
        return
    native = product / "native"
    native.mkdir(exist_ok=True)
    obj = native / "type-name.o"
    run("leanc", "-fPIC", "-c", bridge, "-o", obj)
    with inventory.open() as stream:
        installed = {name for owner, name, _, status, _ in map(json.loads, stream)
                     if owner == "Init.Dynamic" and status in {"added", "existing"}}
    if {"TypeName.mk", "TypeName.typeName"} <= installed:
        consumer = stage / "type-name-consumer.c"
        run("lean", "-R", HERE, "-c", consumer, HERE / "TypeNameConsumer.lean",
            env={**os.environ, "LEAN_PATH": str(artifact)})
        app = stage / "type-name-consumer"
        run("leanc", consumer, obj, HERE / "type_name_consumer.c", "-o", app)
        run(app)


def generate(stage, product, seed, roots, excluded):
    transfer = stage / "transfer"
    artifact = product / "lib"
    inventory = product / "inventory.jsonl"
    omissions = dict.fromkeys(excluded, "explicit exclusion")
    selection = product / "interface-rejections.jsonl"
    run("lake", "build", "omegaAudit", "+OmegaChecks.Interface.Equations", "+OmegaChecks.InitPort.Kernel",
        "+OmegaChecks.InitPort.NativeState")
    run("lake", "env", "lean", "--run", HERE / "Kernel.lean", "--prepare-quot", seed)
    order_file = stage / "candidate-order.json"

    def distribute():
        options = ["--order", order_file] if order_file.exists() else []
        run("lake", "env", "lean", "--run", HERE / "Modules.lean", *options, transfer, seed, artifact, *roots)
        return dict(json.loads((product / "modules.json").read_text()))

    with selection.open("w") as rejected:
        while True:
            exclusions = stage / "exclusions.json"
            exclusions.write_text(json.dumps(sorted(omissions.items())))
            run("lake", "env", "lean", "--run", HERE / "Kernel.lean", seed, transfer, inventory, exclusions,
                *roots, env={**os.environ, "LEAN_ABORT_ON_PANIC": "1"})
            graph = distribute()
            if not order_file.exists():
                try:
                    list(TopologicalSorter(graph).static_order())
                except CycleError:
                    _, order = cyclic_declarations(stage / "candidate-edges.jsonl")
                    order_file.write_text(json.dumps(order))
                    graph = distribute()
            try:
                closure = list(TopologicalSorter(graph).static_order())
            except CycleError:
                new, _ = cyclic_declarations(stage / "candidate-edges.jsonl")
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
    run("lake", "env", "lean", "--run", HERE / "ExportAxioms.lean", artifact, *graph)
    raw_task = stage / "raw-task.c"
    if "OmegaInit.Core" in graph:
        compile_tasks(stage, product, artifact, inventory, raw_task)
    if "OmegaInit.Dynamic" in graph:
        compile_type_name(stage, product, artifact, inventory)
    if "OmegaInit.System.ST" in graph:
        compile_state_runtime(stage, product, artifact, inventory, "Reference", "reference",
                              {"Init.System.ST": {"ST.Prim.mkRef", "ST.mkRef", "ST.Ref.swap", "ST.Ref.set", "ST.Ref.ptrEq"}})
    if "OmegaInit.Control.StateRef" in graph:
        compile_state_runtime(stage, product, artifact, inventory, "StateRef", "state_ref", {
            "Init.Control.StateRef": {"StateRefT'.set"},
            "Init.System.ST": {"ST.mkRef", "ST.Ref.set", "ST.Ref.swap"},
        }, [product / "native" / "reference.o"])
    if "OmegaInit.System.Promise" in graph:
        compile_state_runtime(stage, product, artifact, inventory, "Promise", "promise", {
            "Init.System.Promise": {"IO.Promise.new", "IO.Promise.resolve", "IO.Promise.isResolved", "IO.Promise.result?", "IO.Promise.resultD"},
            "Init.Core": {"Task.pure", "Task.get", "Task.map", "Task.bind"},
        }, [raw_task])
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
