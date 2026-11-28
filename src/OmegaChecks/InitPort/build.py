"""Generate independent, audited kernel modules from the installed Lean Init."""
import argparse
from collections import Counter, defaultdict
from graphlib import CycleError, TopologicalSorter
from path_io_test import check_paths
from generated_native import check_runtime_ir, compile_generated
import json
import omegamath
from hosted import foundation_files, link_other_roots, make_view
import os
from pathlib import Path
from report import report
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
STRICT_SOURCES = ROOT / "strict/OmegaChecks/InitPort"
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
    run("leanc", "-DLEAN_EXPORTING", "-I", HERE, "-c", bridge, "-o", obj)
    with inventory.open() as stream:
        installed = {name for mod, name, _, status, _ in map(json.loads, stream)
                     if mod == "Init.Core" and status in {"added", "existing"}}
    required = {"Task.spawn", "Task.map", "Task.bind", "Task.get", "Task.pure",
                "Task.Priority.default", "Task.Priority.max", "Task.Priority.dedicated"}
    if required <= installed:
        consumer = stage / "task-consumer.c"
        run("lean", "-R", STRICT_SOURCES, "-c", consumer, STRICT_SOURCES / "TaskConsumer.lean",
            env={**os.environ, "LEAN_PATH": str(artifact)})
        app = stage / "task-consumer"
        run("leanc", consumer, obj, HERE / "consumers" / "task_consumer.c", "-o", app)
        run(app)


def install_state_runtime(stage, product, artifact, tool, filename):
    bridge = stage / (filename + ".c")
    run("lake", "env", "lean", "--run", HERE / (tool + "Native.lean"), artifact, bridge)
    if not bridge.exists():
        return []
    native = product / "native"
    native.mkdir(exist_ok=True)
    objects = []
    if tool == "Promise":
        pinned = stage / "promise-result-d.c"
        run("lean", "-R", HERE, "-c", pinned, HERE / "PromiseResultD.lean")
        pinned_object = native / "promise-result-d.o"
        run("leanc", "-DLEAN_EXPORTING", "-I", stage, "-c", HERE / "promise_result_d.c", "-o", pinned_object)
        objects.append(pinned_object)
    obj = native / (filename + ".o")
    run("leanc", "-DLEAN_EXPORTING", "-I", HERE, "-c", bridge, "-o", obj)
    return [obj, *objects]


def has_interfaces(inventory, required):
    with inventory.open() as stream:
        installed = {(mod, name) for mod, name, _, status, _ in map(json.loads, stream)
                     if status in {"added", "existing"}}
    return all((mod, name) in installed for mod, names in required.items() for name in names)


def check_state_consumer(stage, artifact, tool, filename, objects):
    consumer = stage / (filename + "-consumer.c")
    run("lean", "-R", STRICT_SOURCES, "-c", consumer, STRICT_SOURCES / (tool + "Consumer.lean"),
        env={**os.environ, "LEAN_PATH": str(artifact)})
    app = stage / (filename + "-consumer")
    run("leanc", "-I", HERE, consumer, *objects, HERE / "consumers" / (filename + "_consumer.c"), "-o", app)
    run(app)


def compile_state_runtime(stage, product, artifact, inventory, tool, filename, required, extra_sources=()):
    objects = install_state_runtime(stage, product, artifact, tool, filename)
    if objects and has_interfaces(inventory, required):
        check_state_consumer(stage, artifact, tool, filename, [*objects, *extra_sources])


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
        run("lean", "-R", STRICT_SOURCES, "-c", consumer, STRICT_SOURCES / "TypeNameConsumer.lean",
            env={**os.environ, "LEAN_PATH": str(artifact)})
        app = stage / "type-name-consumer"
        run("leanc", consumer, obj, HERE / "consumers" / "type_name_consumer.c", "-o", app)
        run(app)
        safe_source = (STRICT_SOURCES / "TypeNameConsumer.lean").read_text().replace("public unsafe def", "public def")
        rejected = subprocess.run(["lean", "--stdin"], input=safe_source, text=True, capture_output=True,
                                  env={**os.environ, "LEAN_PATH": str(artifact)})
        if rejected.returncode == 0 or "uses unsafe declaration 'Omega.TypeName.mk'" not in rejected.stdout + rejected.stderr:
            raise ValueError("ordinary code could assign an arbitrary name to a type")



def generate(stage, product, seed, roots, excluded, original_seed):
    transfer = stage / "transfer"
    artifact = product / "lib"
    inventory = product / "inventory.jsonl"
    omissions = dict.fromkeys(excluded, "explicit exclusion")
    selection = product / "interface-rejections.jsonl"
    run("lake", "build", "omegaAudit", "+OmegaChecks.Interface.Equations", "+OmegaChecks.InitPort.Kernel",
        "+OmegaChecks.InitPort.GeneratedNative", "+OmegaChecks.InitPort.MacroMethodsNative")
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
        if has_interfaces(inventory, {"Init.System.ST": {"ST.Prim.Ref.put", "ST.Ref.put"}}):
            check_state_consumer(stage, artifact, "ReferencePut", "ref_put", [product / "native/reference.o"])
            source = (STRICT_SOURCES / "ReferencePutConsumer.lean").read_text().replace("public unsafe def", "public def")
            safe = subprocess.run(["lean", "--stdin"], input=source, text=True, capture_output=True,
                                  env={**os.environ, "LEAN_PATH": str(artifact)})
            if safe.returncode == 0 or any(f"uses unsafe declaration '{name}'" not in safe.stdout + safe.stderr
                                           for name in ("Omega.ST.Prim.Ref.put", "Omega.ST.Ref.put")):
                raise ValueError("safe client did not reject both unsafe reference writes")
        if has_interfaces(inventory, {"Init.System.ST": {"ST.Prim.Ref.modifyUnsafe"}}):
            check_state_consumer(stage, artifact, "ReferenceModify", "ref_modify", [product / "native/reference.o"])
        pure_state = {"Init.System.ST": {"Void.mk", "ST.pure", "ST.bind", "EST.pure", "EST.bind",
                                         "EST.throw", "EST.tryCatch", "runST", "runEST", "EST.Out.ok.elim",
                                         "EST.Out.error.elim", "instMonadST", "instMonadEST", "instMonadExceptOfEST",
                                         "instMonadAttachST", "instMonadAttachEST", "instInhabitedST", "instInhabitedEST",
                                         "instMonadFinallyST", "instMonadFinallyEST", "instMonadLiftSTEST"}}
        if has_interfaces(inventory, pure_state):
            check_state_consumer(stage, artifact, "PureState", "pure_state", [product / "native" / "reference.o"])
            check_runtime_ir(stage, artifact, "Reference", "PureState")
    if "OmegaInit.Data.Random" in graph:
        install_state_runtime(stage, product, artifact, "Random", "random-state")
    if "OmegaInit.Control.StateRef" in graph:
        compile_state_runtime(stage, product, artifact, inventory, "StateRef", "state_ref", {
            "Init.Control.StateRef": {"StateRefT'.set"},
            "Init.System.ST": {"ST.mkRef", "ST.Ref.set", "ST.Ref.swap"},
        }, [product / "native" / "reference.o"])
    if "OmegaInit.System.IO" in graph:
        compile_state_runtime(stage, product, artifact, inventory, "TaskIO", "task_io", {
            "Init.System.IO": {"IO.getTaskState", "IO.hasFinished", "IO.wait", "IO.waitAny", "IO.waitAny'", "IO.cancel", "IO.checkCanceled",
                               *(f"{ns}.{name}" for ns in ("BaseIO", "EIO", "IO")
                                 for name in ("asTask", "mapTask", "bindTask", "chainTask", "mapTasks"))},
        })
        paths = install_state_runtime(stage, product, artifact, "PathIO", "path_io")
        path_interfaces = {"Init.System.IO": {"IO.getEnv", "IO.FS.createDir", "IO.FS.removeDir",
                                              "IO.FS.removeFile", "IO.FS.rename", "IO.FS.hardLink", "IO.FS.realPath",
                                              "IO.FS.createTempDir", "IO.appPath", "IO.currentDir", "IO.Process.getCurrentDir",
                                              "IO.Process.setCurrentDir", "System.FilePath.readDir",
                                              *(f"IO.FS.Handle.{op}" for op in ("mk", "lock", "tryLock", "unlock", "isTty",
                                                                                 "flush", "rewind", "truncate", "read",
                                                                                 "write", "getLine", "putStr"))}}
        if paths and has_interfaces(inventory, path_interfaces):
            check_paths(stage, artifact, paths[0], product / "native" / "task_io.o",
                        check_read_into=has_interfaces(inventory, {"Init.System.IO": {"IO.FS.Handle.readBinToEndInto"}}))
    if "OmegaInit.System.Promise" in graph:
        compile_state_runtime(stage, product, artifact, inventory, "Promise", "promise", {
            "Init.System.Promise": {"IO.Promise.new", "IO.Promise.resolve", "IO.Promise.isResolved", "IO.Promise.result?", "IO.Promise.resultD"},
            "Init.Core": {"Task.pure", "Task.get", "Task.map", "Task.bind"},
        }, [raw_task])
    sharing = []

    def install_sharing():
        sharing.extend(install_state_runtime(stage, product, artifact, "ShareCommon", "share_common"))

    def check_sharing(objects):
        required = {"Init.ShareCommon": {"ShareCommon.StateFactory.mk", "ShareCommon.State.mk",
                                         "ShareCommon.State.shareCommon", "ShareCommonM.run"}}
        if sharing and has_interfaces(inventory, required):
            if objects is None:
                check_runtime_ir(stage, artifact, "ShareCommon", "ShareCommon")
            else:
                check_state_consumer(stage, artifact, "ShareCommon", "share_common", objects)
        if sharing and has_interfaces(inventory, {"Init.ShareCommon": {"ShareCommon.Object.eq", "ShareCommon.Object.hash"}}):
            if objects is None:
                check_runtime_ir(stage, artifact, "ShareCommon", "ShareObject")
            else:
                check_state_consumer(stage, artifact, "ShareObject", "share_object", objects)

    string_interfaces = {
        "Init.Data.String.Bootstrap": {"String.push", "String.mk", "String.Internal.length",
                                       "String.Internal.extract", "String.Internal.append"},
        "Init.Data.String.Defs": {"String.append", "String.toUTF8"},
        "Init.Prelude": {"String.ofList", "String.utf8ByteSize", "String.toByteArray", "String.decEq", "String.hash"},
        "Init.Data.String.Basic": {"String.toList", "String.data", "String.decidableLT", "ByteArray.validateUTF8",
                                   *(f"String.Pos.Raw.{n}" for n in ("get", "next", "prev", "atEnd", "isValid"))},
    }
    mixed_interfaces = {"Init.Prelude": {"Lean.Macro.instMonadQuotationMacroM", "Lean.Syntax",
                                          "Lean.Syntax.getNumArgs", "Lean.defaultMaxRecDepth"}}
    compile_generated(stage, product, graph, original_seed.parents[1] / "ir",
                      original_seed=original_seed, before_owner={"OmegaInit.ShareCommon": install_sharing},
                      check_sharing=check_sharing,
                      check_syntax_array=has_interfaces(inventory, {"Init.Prelude": {"Lean.TSyntaxArray.mkImpl", "Lean.TSyntaxArray.rawImpl"}}),
                      check_array_map=has_interfaces(inventory, {"Init.Data.Array.Basic": {"Array.mapMUnsafe", "Array.mapFinIdxMUnsafe"}}),
                      check_macro_writer=has_interfaces(inventory, {"Init.Prelude": {"Lean.Macro.mkMethodsImp"}}),
                      check_macro_reader=has_interfaces(inventory, {"Init.Prelude": {"Lean.Macro.getMethodsImp"}}),
                      check_list_pointer=has_interfaces(inventory, {"Init.Util": {"ptrEqList"}}),
                      check_pointer_hash=has_interfaces(inventory, {"Init.ShareCommon": {"ShareCommon.Object.ptrHash"}}),
                      check_address_callback=has_interfaces(inventory, {"Init.Util": {"withPtrAddrUnsafe"}}),
                      check_shared_pointer=has_interfaces(inventory, {"Init.ShareCommon": {"ShareCommon.Object.ptrEq"}}),
                      check_pointer_comparison=has_interfaces(inventory, {"Init.Util": {"ptrEq", "withPtrEqUnsafe"}}),
                      check_guarded_pointer=has_interfaces(inventory, {"Init.Util": {"withPtrEq"}}),
                      check_address=has_interfaces(inventory, {"Init.Util": {"ptrAddrUnsafe"}}),
                      check_exclusive=has_interfaces(inventory, {"Init.Util": {"isExclusiveUnsafe"}}),
                      check_borrowed_arrays=has_interfaces(inventory, {
                          "Init.Prelude": {"Array.getInternalBorrowed", "Array.get!InternalBorrowed"},
                          "Init.Data.Array.Basic": {"Array.ugetBorrowed"},
                      }),
                      check_effects=has_interfaces(inventory, {"Init.System.IO": {"unsafeBaseIO", "unsafeEIO", "unsafeIO"}}),
                      check_persistent=has_interfaces(inventory, {"Init.System.IO": {"Runtime.markPersistent"}}),
                      check_mixed=has_interfaces(inventory, mixed_interfaces),
                      check_dynamic=has_interfaces(inventory, {"Init.Dynamic": {
                          "TypeName.mk", "Dynamic.mk", "Dynamic.typeName", "Dynamic.get?"}}),
                      check_thunks=has_interfaces(inventory, {"Init.Core": {
                          "Thunk.mk", "Thunk.pure", "Thunk.get", "Thunk.map", "Thunk.bind",
                          "Thunk.fn", "Thunk.fnImpl", "instInhabitedThunk"}}),
                      check_names=has_interfaces(inventory, {"Init.Prelude": {
                          "Lean.Name.append", "Lean.addMacroScope", "Lean.extractMacroScopes",
                          "Lean.MacroScopesView.review"}}),
                      check_toolchain=has_interfaces(inventory, {"Init.Meta.Defs": {
                          "Lean.getGithash", "Lean.githash", "Lean.version.getSpecialDesc",
                          "Lean.version.specialDesc", "Lean.version.getIsRelease", "Lean.version.isRelease",
                          "Lean.Internal.isStage0", "Lean.Internal.hasLLVMBackend"}}),
                      check_strings=has_interfaces(inventory, string_interfaces),
                      check_string_marks=has_interfaces(inventory, {
                          "Init.Data.String.Defs": {"String.markLinear", "String.propagateMark"},
                          "Init.Data.String.Bootstrap": {"String.push"},
                      }),
                      check_byte_marks=has_interfaces(inventory, {
                          "Init.Data.ByteArray.Basic": {"ByteArray.markLinear", "ByteArray.propagateMark",
                                                        "ByteArray.set!", "ByteArray.copySlice"},
                          "Init.Prelude": {"ByteArray.push", "String.ofByteArray"},
                          "Init.Data.String.Defs": {"String.toUTF8"},
                      }),
                      check_list_search=has_interfaces(inventory, {
                          "Init.Data.List.Control": {"List.anyM", "List.allM"},
                          "Init.Control.Id": {"Id.instMonad"},
                          "Init.Prelude": {"ite"},
                      }),
                      check_decoding=has_interfaces(inventory, {
                          "Init.Data.String.Basic": {"ByteArray.utf8Decode?", "String.Pos.Raw.get?"},
                          "Init.Data.String.Decode": {"ByteArray.utf8DecodeChar?", "String.utf8EncodeCharFast"},
                      }),
                      check_bootstrap=has_interfaces(inventory, {"Init.Data.String.Bootstrap": {
                          "String.Internal.nextWhile", "Substring.Raw.Internal.takeWhile",
                          "String.Internal.foldl", "String.push", "Substring.Raw.Internal.toString",
                          "String.Internal.intercalate"}}),
                      check_rat=has_interfaces(inventory, {
                          "Init.Data.Rat.Basic": {"mkRat", "instReprRat", "instToStringRat"},
                          "Init.Data.String.Defs": {"String.append"},
                          "Init.Data.Nat.Gcd": {"Nat.gcd"},
                      }),
                      check_literals=has_interfaces(inventory, {"Init.Prelude": {"String.ofList", "Char.ofNat"}}))
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
    parser.add_argument("--isolated-only", action="store_true",
                        help="publish only the independently replayed library for prelude consumers")
    parser.add_argument("--exclude", action="append", default=[],
                        help="omit a generated candidate; declarations already in the seed cannot be excluded")
    parser.add_argument("--require-complete", action="store_true",
                        help="require checked implementations or unconditional logical boundaries at all official sites")
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
        generate(stage, product, stage / "seed", roots, args.exclude, seed)
        if not args.modules:
            report(product, require_complete=args.require_complete)
            omegamath.build(product, product / "lib", args.j, product / "omegamath-audit.txt")
        if not args.isolated_only:
            library = product / "lib"
            hosted = product / "hosted"
            make_view(library, hosted, foundation_files(library))
            link_other_roots(library, hosted)
            consumer = roots[0].replace("Init", "OmegaInit", 1) if args.modules else "OmegaMath"
            probe = f"import {consumer}\n"
            xor_module = "Init.Data.Nat.Bitwise.Basic"
            check_xor = has_interfaces(product / "inventory.jsonl", {xor_module: {"Nat.xor"}})
            if check_xor:
                probe += "import OmegaInit.Data.Nat.Bitwise.Basic\n"
                x = 2**127 + 2**73 + 1
                y = 2**131 + 2**73 + 13
                probe += "example : Omega.Nat.xor 3 5 = 6 := rfl\n"
                probe += f"example : Omega.Nat.xor {x} {y} = {x ^ y} := rfl\n"
            if consumer == "OmegaMath" or consumer == "OmegaInit.Prelude":
                probe += "example {p q : Prop} (h : Omega.And p q) : p := Omega.And.left h\n"
            hosted_env = {**os.environ, "LEAN_PATH": str(hosted)}
            run("lean", "--stdin", text=True, input=probe, env=hosted_env)
            run("lean", HERE / "consumers/QuotientConsumer.lean", env=hosted_env)
            if (hosted / "OmegaInit/Data/List/Scan/Basic.olean").is_file():
                run("lean", HERE / "consumers/ListScanConsumer.lean", env=hosted_env)
        product.rename(target)


if __name__ == "__main__":
    main()
