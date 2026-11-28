"""Compile checked definitions in generated Init owners and link an ordinary C consumer."""
from concurrent.futures import ThreadPoolExecutor
from filecmp import cmp
from graphlib import TopologicalSorter
import os
from pathlib import Path
import re
import subprocess
import sysconfig

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
STRICT_SOURCES = ROOT / "strict/OmegaChecks/InitPort"
CONTROL = ("OmegaInit.Control.Except", "OmegaInit.Control.Option", "OmegaInit.Control.State")


def run(*args, **options):
    subprocess.run(args, check=True, cwd=ROOT, **options)


def compile_object(paths):
    source, obj = paths
    obj.parent.mkdir(exist_ok=True, parents=True)
    run("leanc", "-DLEAN_EXPORTING", "-I", HERE, "-c", source, "-o", obj)
    return obj


def init_suffix(source):
    # The pinned C emitter spells the package in all three module initializer symbols.
    match = re.search(r"^LEAN_EXPORT lean_object\* runtime_initialize_(\w+)\(uint8_t builtin\) \{",
                      source.read_text(), re.MULTILINE)
    return match.group(1) if match else None


def link_owner(out, directory, parts):
    """Keep each input's private C symbols local and sequence its original initializers."""
    directory.mkdir(parents=True, exist_ok=True)
    phases = ("runtime_initialize_", "meta_initialize_", "initialize_")
    suffix = init_suffix(parts[0])
    if suffix is None or any(init_suffix(part) != suffix for part in parts):
        raise ValueError(f"inconsistent native module initializers in {parts}")
    compiled = []
    dispatch = ["#include <lean/lean.h>"]
    for index, part in enumerate(parts):
        flags = []
        for phase in phases:
            name = phase + suffix
            renamed = f"omega_part_{index}_{name}"
            flags.append(f"-D{name}={renamed}")
            dispatch.append(f"extern lean_obj_res {renamed}(uint8_t);")
        obj = directory / f"{index}.o"
        run("leanc", "-DLEAN_EXPORTING", "-I", HERE, "-I", part.parent, *flags, "-c", part, "-o", obj)
        compiled.append(obj)
    for phase in phases:
        name = phase + suffix
        dispatch += [f"LEAN_EXPORT lean_obj_res {name}(uint8_t builtin) {{", "  lean_obj_res result;"]
        for index in range(len(parts) - 1):
            dispatch += [f"  result = omega_part_{index}_{name}(builtin);",
                         "  if (lean_io_result_is_error(result)) return result;", "  lean_dec_ref(result);"]
        dispatch += [f"  return omega_part_{len(parts) - 1}_{name}(builtin);", "}"]
    wrapper = directory / "init.c"
    wrapper.write_text("\n".join(dispatch) + "\n")
    compiled.append(compile_object((wrapper, directory / "init.o")))
    out.parent.mkdir(parents=True, exist_ok=True)
    combined = directory / "combined.o"
    run("ld", "-r", "-o", combined, *compiled)
    combined.replace(out)
    return out


def match_cached_seed(owner, seed):
    """Reuse the local C output only when both compiled module payloads and signatures match."""
    relative = Path(*owner.split("."))
    local = ROOT / ".lake/build/omega-strict"
    source = (local / "ir" / relative).with_suffix(".c")
    if not source.is_file():
        return None
    for suffix in (".olean", ".olean.server", ".olean.private", ".ir", ".ir.sig"):
        original = (seed / relative).with_suffix(suffix)
        cached = (local / "lib/lean" / relative).with_suffix(suffix)
        if not original.is_file() or not cached.is_file() or not cmp(original, cached, shallow=False):
            return None
    return source


def check_runtime_ir(stage, library, adapter, consumer):
    check = stage / (consumer + "-ir")
    check.mkdir()
    source = check / "extern.c"
    run("lake", "env", "lean", "--run", HERE / (adapter + "Native.lean"), "--interpreter", library, source)
    shim = check / ("extern" + (sysconfig.get_config_var("SHLIB_SUFFIX") or ".so"))
    run("leanc", "-shared", "-fPIC", "-DLEAN_EXPORTING", "-I", HERE, source, "-o", shim)
    run("lean", "-R", STRICT_SOURCES, "-o", check / (consumer + "Consumer.olean"), STRICT_SOURCES / (consumer + "Consumer.lean"),
        env={**os.environ, "LEAN_PATH": str(library)})
    run("lake", "env", "lean", "--load-dynlib=" + str(shim), "--run", HERE / "consumers" / (consumer + "IRConsumer.lean"),
        library, check)


def check_linear_marks(stage, library, inputs, kind):
    client = stage / f"{kind}-mark-consumer.c"
    consumer = STRICT_SOURCES / f"{kind.capitalize()}MarkConsumer.lean"
    run("lean", "-R", STRICT_SOURCES, "-c", client, consumer, env={**os.environ, "LEAN_PATH": str(library)})
    app = stage / f"check-{kind}-mark"
    run("leanc", "-I", HERE, client, HERE / f"consumers/{kind}_mark_consumer.c", *inputs, "-o", app)
    base = {k: v for k, v in os.environ.items() if k != "LEAN_ABORT_ON_NONLINEAR"}
    operations = ["mark", "remark", "propagate", "propagate-fresh", "propagate-unmarked", "push"]
    if kind == "byte":
        operations.extend(["set", "set-out", "copy", "text"])
    for value in ["", "hé中"]:
        for abort in [False, True]:
            env = {**base, "LEAN_ABORT_ON_NONLINEAR": "1"} if abort else base
            for operation in operations:
                for share in ["", "shared-"]:
                    case = share + operation
                    native, strict = (subprocess.run([app, variant, case, value], env=env, capture_output=True)
                                      for variant in ["native", "strict"])
                    if native.returncode != strict.returncode or native.stdout != strict.stdout:
                        raise ValueError(f"{kind} {case}, {value!r}, abort={abort}: "
                                         f"native {native.returncode} {native.stdout!r}, "
                                         f"strict {strict.returncode} {strict.stdout!r}")
                    if native.returncode != 0 and not (abort and share and
                            operation in ["remark", "propagate", "push", "set", "copy"]):
                        native.check_returncode()


def compile_generated(stage, product, graph, seed_ir, owners=None, *, original_seed=None, before_owner=None,
                      check_sharing=None, check_array_map=False, check_macro_reader=False, check_macro_writer=False, check_syntax_array=False,
                      check_strings=True, check_string_marks=False, check_byte_marks=False, check_literals=True, check_mixed=True, check_rat=True, check_bootstrap=True,
                      check_list_search=True, check_decoding=True, check_names=True, check_toolchain=True, check_thunks=False, check_persistent=False, check_exclusive=False,
                      check_guarded_pointer=False, check_effects=False, check_borrowed_arrays=False, check_address=False, check_pointer_comparison=False, check_shared_pointer=False,
                      check_list_pointer=False, check_pointer_hash=False, check_address_callback=False, check_dynamic=False):
    """Compile generated owners in import order and preserve the native symbols of existing owners."""
    requested = set(graph if owners is None else owners)
    selected = [owner for owner in TopologicalSorter(graph).static_order()
                if owner in requested and (owner == "OmegaInit" or owner.startswith("OmegaInit."))]
    if not selected:
        return []
    sources = stage / "generated-native"
    library = product / "lib"
    seed_files = {owner: (seed_ir / Path(*owner.split("."))).with_suffix(".c") for owner in graph}
    seed = stage / "seed"
    if seed.is_dir():
        seed_owners = {owner for owner in graph if (seed / Path(*owner.split("."))).with_suffix(".olean").is_file()}
    else:
        seed_owners = {owner for owner, source in seed_files.items() if source.is_file()}
    if original_seed is not None:
        for owner in seed_owners:
            if not seed_files[owner].is_file():
                cached = match_cached_seed(owner, original_seed)
                if cached is not None:
                    seed_files[owner] = cached
    modes = {owner: "mixed=" if seed_files[owner].is_file() else "layouts=" for owner in seed_owners}
    env = {**os.environ, "LEAN_ABORT_ON_PANIC": "1"}
    callbacks = before_owner or {}
    string_owner = "OmegaInit.Data.String.Basic"
    string_modules = {
        "OmegaInit.Prelude": "literal",
        "OmegaInit.Data.String.Bootstrap": "string-bootstrap",
        "OmegaInit.Data.String.Defs": "string-defs",
        string_owner: "string-list",
    }
    string_sources = []
    for owner, filename in string_modules.items():
        if owner not in selected:
            continue
        source = stage / (filename + ".c")
        run("lake", "env", "lean", "--run", HERE / "LiteralNative.lean", library, source, owner, env=env)
        if source.exists():
            compile_object((source, product / "native" / (filename + ".o")))
            string_sources.append(source)
            if owner not in seed_owners:
                modes[owner] = "mixed="
    if "OmegaInit.Data.Random" in selected and (stage / "random-state.c").is_file():
        modes["OmegaInit.Data.Random"] = "mixed="
    if "OmegaInit.Dynamic" in selected and (stage / "type-name.c").is_file():
        modes["OmegaInit.Dynamic"] = "mixed="
    runtime_sources = {"OmegaInit.Control.StateRef": "state_ref.c", "OmegaInit.Dynamic": "type-name.c",
                       "OmegaInit.ShareCommon": "share_common.c"}
    literals = stage / "literal.c"
    macro_source = stage / "macro-methods.c"
    if "OmegaInit.Prelude" in selected:
        run("lake", "env", "lean", "--run", HERE / "GeneratedNative.lean", library, sources,
            "layouts=OmegaInit.Prelude", env=env)
        run("lake", "env", "lean", "--run", HERE / "MacroMethodsNative.lean", library, macro_source, env=env)
        if macro_source.is_file():
            macro_client = stage / "macro-methods-consumer.c"
            run("lean", "-R", STRICT_SOURCES, "-c", macro_client, STRICT_SOURCES / "MacroMethodsConsumer.lean",
                env={**os.environ, "LEAN_PATH": str(library)})
            app = stage / "check-macro-methods"
            flags = ["-DCHECK_MACRO_METHODS_IMP"] if check_macro_reader else []
            if check_macro_writer:
                flags.append("-DCHECK_MACRO_MK_METHODS_IMP")
            run("leanc", *flags, macro_source, macro_client, HERE / "consumers" / "macro_methods_consumer.c", "-o", app)
            run(app)
            if literals.is_file():
                combined = product / "native/literal.o"
                link_owner(combined, stage / "prelude-bridges", [literals, macro_source])
            else:
                compile_object((macro_source, product / "native/macro-methods.o"))
    requests = [modes.get(owner, "") + owner for owner in selected]
    if owners is not None and "OmegaInit.Control.State" in requested and "OmegaInit.Control.Basic" not in requested:
        requests.insert(0, "layouts=OmegaInit.Control.Basic")
    pending = []

    def flush():
        if pending:
            run("lake", "env", "lean", "--run", HERE / "GeneratedNative.lean",
                library, sources, *pending, env=env)
            pending.clear()

    for request in requests:
        owner = request.split("=")[-1]
        callback = callbacks.get(owner)
        if callback:
            flush()
            callback()
        if owner in runtime_sources and owner not in seed_owners and (stage / runtime_sources[owner]).is_file():
            modes[owner] = "mixed="
            request = "mixed=" + owner
        pending.append(request)
        if len(pending) == 32:
            flush()
    flush()

    native = product / "native"
    adapters = {}
    for obj in native.glob("*.o"):
        source = stage / obj.with_suffix(".c").name
        if source.is_file() and (suffix := init_suffix(source)) is not None:
            adapters[suffix] = (source, obj)

    def compile_owner(source):
        relative = source.relative_to(sources)
        owner = ".".join(relative.with_suffix("").parts)
        obj = (native / "generated" / relative).with_suffix(".o")
        if modes.get(owner) == "mixed=":
            parts = [seed_files[owner]] if owner in seed_owners else []
            if adapter := adapters.get(init_suffix(source)):
                adapter_source, obj = adapter
                parts.append(adapter_source)
                if owner == "OmegaInit.Prelude" and adapter_source == literals and macro_source.is_file():
                    parts.append(macro_source)
            parts.append(source)
            obj = link_owner(obj, stage / "mixed-native" / owner, parts)
        else:
            compile_object((source, obj))
        return owner, obj

    with ThreadPoolExecutor(max_workers=4) as pool:
        objects = dict(pool.map(compile_owner, sorted(sources.rglob("*.c"))))

    def reachable(roots):
        seen = set()
        pending = list(roots)
        while pending:
            owner = pending.pop()
            if owner not in seen:
                seen.add(owner)
                pending.extend(graph.get(owner, ()))
        return seen

    def dependency_objects(dependencies):
        inputs = []
        for owner in sorted(dependencies):
            obj = objects.get(owner)
            if obj is None:
                suffix = owner.replace(".", "_")
                adapter = adapters.get(suffix) or adapters.get("trureturing_" + suffix)
                if adapter:
                    obj = adapter[1]
                elif seed_files[owner].is_file():
                    obj = (stage / "original-native" / Path(*owner.split("."))).with_suffix(".o")
                    compile_object((seed_files[owner], obj))
                else:
                    raise ValueError(f"missing native dependency {owner}")
            inputs.append(obj)
        return inputs

    array_owner = "OmegaInit.Data.Array.Basic"
    if check_borrowed_arrays and array_owner in selected:
        required = reachable([array_owner])
        if required.issubset(selected) and all(seed_files[d].is_file() for d in required & seed_owners):
            app = stage / "check-borrowed-arrays"
            consumer = stage / "borrowed-array-consumer.c"
            run("lean", "-R", STRICT_SOURCES, "-c", consumer, STRICT_SOURCES / "BorrowedArrayConsumer.lean",
                env={**os.environ, "LEAN_PATH": str(library)})
            run("leanc", consumer, HERE / "consumers/borrowed_array_consumer.c", *dependency_objects(required), "-o", app)
            run(app)

    share_owner = "OmegaInit.ShareCommon"
    if check_sharing and share_owner in selected:
        dependencies = reachable([share_owner])
        complete = dependencies.issubset(selected) and all(seed_files[d].is_file() for d in dependencies & seed_owners)
        check_sharing(dependency_objects(dependencies) if complete else None)

    if check_thunks and "OmegaInit.Core" in selected:
        dependencies = reachable(["OmegaInit.Core"])
        if dependencies.issubset(selected) and all(seed_files[d].is_file() for d in dependencies & seed_owners):
            client = stage / "thunk-consumer.c"
            run("lean", "-R", STRICT_SOURCES, "-c", client, STRICT_SOURCES / "ThunkConsumer.lean",
                env={**os.environ, "LEAN_PATH": str(library)})
            app = stage / "check-thunk"
            run("leanc", client, HERE / "consumers" / "thunk_consumer.c", *dependency_objects(dependencies), "-o", app)
            run(app, timeout=30)

    observations = [(check_syntax_array, "OmegaInit.Prelude", "SyntaxArray", "Omega.Lean.TSyntaxArray.mkImpl"),
                    (check_array_map, "OmegaInit.Data.Array.Basic", "UnsafeArrayMap", "Omega.Array.mapMUnsafe"),
                    (check_dynamic, "OmegaInit.Dynamic", "DynamicValue", None),
                    (check_persistent, "OmegaInit.System.IO", "Persistent", "Omega.Runtime.markPersistent"),
                    (check_address, "OmegaInit.Util", "Address", "Omega.ptrAddrUnsafe"),
                    (check_exclusive, "OmegaInit.Util", "Exclusive", "Omega.isExclusiveUnsafe"),
                    (check_address_callback, "OmegaInit.Util", "AddressCallback", "Omega.withPtrAddrUnsafe"),
                    (check_list_pointer, "OmegaInit.Util", "ListPointer", "Omega.ptrEqList"),
                    (check_pointer_hash, "OmegaInit.ShareCommon", "PointerHash", "Omega.ShareCommon.Object.ptrHash"),
                    (check_shared_pointer, "OmegaInit.ShareCommon", "SharedPointer", "Omega.ShareCommon.Object.ptrEq"),
                    (check_pointer_comparison, "OmegaInit.Util", "PointerComparison", "Omega.ptrEq"),
                    (check_guarded_pointer, "OmegaInit.Util", "GuardedPointer", None),
                    (check_effects, "OmegaInit.System.IO", "EffectRun", "Omega.unsafeBaseIO")]
    for enabled, owner, client_name, declaration in observations:
        if not enabled or owner not in selected:
            continue
        required = reachable([owner])
        if required.issubset(selected) and all(seed_files[d].is_file() for d in required & seed_owners):
            stem = client_name.lower()
            client = stage / f"{stem}-consumer.c"
            consumer = STRICT_SOURCES / f"{client_name}Consumer.lean"
            env = {**os.environ, "LEAN_PATH": str(library)}
            run("lean", "-R", STRICT_SOURCES, "-c", client, consumer, env=env)
            app = stage / f"check-{stem}"
            run("leanc", client, HERE / f"consumers/{stem}_consumer.c", *dependency_objects(required), "-o", app)
            run(app)
            if declaration is None:
                continue
            safe = consumer.read_text().replace("public unsafe def", "public def")
            result = subprocess.run(["lean", "--stdin"], input=safe, text=True, env=env, capture_output=True)
            unsafe_names = [declaration] if client_name != "EffectRun" else [
                "Omega.unsafeBaseIO", "Omega.unsafeEIO", "Omega.unsafeIO"]
            if client_name == "UnsafeArrayMap":
                unsafe_names = ["Omega.Array.mapMUnsafe", "Omega.Array.mapFinIdxMUnsafe"]
            if client_name == "PointerComparison":
                unsafe_names = ["Omega.ptrEq", "Omega.withPtrEqUnsafe"]
            if client_name == "SyntaxArray":
                unsafe_names.append("Omega.Lean.TSyntaxArray.rawImpl")
            for name in unsafe_names:
                if result.returncode == 0 or f"uses unsafe declaration '{name}'" not in result.stdout + result.stderr:
                    raise ValueError(f"safe client did not reject {name}")
            if client_name == "EffectRun":
                oracle = stage / "effect-oracle"
                oracle.mkdir()
                official = oracle / consumer.name
                official.write_text(consumer.read_text().replace("OmegaInit.", "Init.").replace("Omega.", ""))
                oracle_c = oracle / "consumer.c"
                run("lean", "-R", oracle, "-c", oracle_c, official)
                executable = oracle / "check"
                run("leanc", oracle_c, HERE / "consumers/effectrun_consumer.c", "-o", executable)
                run(executable)

    if (check_string_marks or check_byte_marks) and "OmegaInit.Data.String.Defs" in selected:
        required = reachable(["OmegaInit.Data.String.Defs"])
        if required.issubset(selected) and all(seed_files[d].is_file() for d in required & seed_owners):
            inputs = dependency_objects(required)
            if check_string_marks:
                check_linear_marks(stage, library, inputs, "string")
            if check_byte_marks:
                check_linear_marks(stage, library, inputs, "byte")

    if len(string_sources) == len(string_modules) and check_strings:
        list_client = stage / "string-list-consumer.c"
        run("lean", "-R", STRICT_SOURCES, "-o", stage / "StringListConsumer.olean", "-c", list_client,
            STRICT_SOURCES / "StringListConsumer.lean",
            env={**os.environ, "LEAN_PATH": str(library)})
        dependencies = reachable([string_owner])
        missing = sorted(name for name in dependencies & seed_owners if not seed_files[name].is_file())
        complete = not missing and (owners is None or dependencies.issubset(selected))
        if not complete:
            # Detached and selectively compiled products need only the string adapters for this consumer.
            inputs = string_sources
        else:
            inputs = dependency_objects(dependencies)
        application = stage / "check-string-list"
        run("leanc", "-I", HERE, list_client, HERE / "consumers" / "string_list_consumer.c", *inputs, "-o", application)
        run(application)
        shim = stage / ("string-extern" + (sysconfig.get_config_var("SHLIB_SUFFIX") or ".so"))
        if complete and check_decoding:
            run("leanc", "-shared", "-fPIC", "-DLEAN_EXPORTING", *inputs, "-o", shim)
            initializer = init_suffix(stage / "string-list.c")
            if initializer is None:
                raise ValueError("missing strict String.Basic initializer")
            loader = f"--plugin={shim}=runtime_initialize_{initializer}"
            options = ["--decode"]
            if check_toolchain and "OmegaInit.Meta.Defs" in dependencies:
                run("lake", "env", "lean", loader, "--run", HERE / "ToolchainInfo.lean", library)
        else:
            run("leanc", "-shared", "-fPIC", "-DLEAN_EXPORTING", "-I", HERE, *string_sources, "-o", shim)
            loader = "--load-dynlib=" + str(shim)
            options = []
        run("lake", "env", "lean", loader, "--run", HERE / "consumers" / "StringListIRConsumer.lean", library, stage, *options)
    search_owner = "OmegaInit.Data.List.Control"
    if check_list_search and search_owner in objects and literals.is_file():
        dependencies = reachable([search_owner, "OmegaInit.Control.Id"])
        if dependencies.issubset(selected) and all(seed_files[d].is_file() for d in dependencies & seed_owners):
            client = stage / "list-search-consumer.c"
            run("lean", "-R", STRICT_SOURCES, "-c", client, STRICT_SOURCES / "ListSearchConsumer.lean",
                env={**os.environ, "LEAN_PATH": str(library)})
            application = stage / "check-list-search"
            run("leanc", client, HERE / "consumers" / "list_search_consumer.c", *dependency_objects(dependencies), "-o", application)
            run(application)
    bootstrap = "OmegaInit.Data.String.Bootstrap"
    if check_bootstrap and bootstrap in objects and literals.is_file():
        dependencies = reachable([bootstrap])
        if dependencies.issubset(selected) and all(seed_files[d].is_file() for d in dependencies & seed_owners):
            client = stage / "string-bootstrap-consumer.c"
            run("lean", "-R", STRICT_SOURCES, "-c", client, STRICT_SOURCES / "StringBootstrapConsumer.lean",
                env={**os.environ, "LEAN_PATH": str(library)})
            application = stage / "check-string-bootstrap"
            run("leanc", "-I", HERE, client, HERE / "consumers" / "string_bootstrap_consumer.c", *dependency_objects(dependencies),
                "-o", application)
            run(application)
    rat_owner = "OmegaInit.Data.Rat.Basic"
    if check_rat and rat_owner in objects:
        dependencies = reachable([rat_owner])
        available = all(seed_files[owner].is_file() for owner in dependencies & seed_owners)
        # The literal bridge verifies that this product uses the physical kernel Nat and UTF-8 layout.
        if available and dependencies.issubset(selected) and literals.is_file():
            client = stage / "rat-format-consumer.c"
            run("lean", "-R", STRICT_SOURCES, "-c", client, STRICT_SOURCES / "RatFormatConsumer.lean",
                env={**os.environ, "LEAN_PATH": str(library)})
            application = stage / "check-rat-format"
            run("leanc", "-I", HERE, client, HERE / "consumers" / "rat_format_consumer.c", *dependency_objects(dependencies),
                "-o", application)
            run(application)
    if not set(CONTROL).issubset(selected):
        return []

    control_deps = reachable(CONTROL)
    sources.mkdir(exist_ok=True, parents=True)
    consumer = sources / "consumer.c"
    run("lean", "-R", STRICT_SOURCES, "-o", sources / "GeneratedControlConsumer.olean", "-c", consumer,
        STRICT_SOURCES / "GeneratedControlConsumer.lean", env={**os.environ, "LEAN_PATH": str(library)})
    missing = sorted(owner for owner in control_deps & seed_owners if not seed_files[owner].is_file())
    if missing:
        run("lake", "env", "lean", "--run", HERE / "GeneratedNative.lean", "--check-control", library, sources,
            env=env)
        print("Checked generated control consumers using packaged IR. Seed C files unavailable for "
              + ", ".join(missing), flush=True)
        return None
    inputs = [obj for owner, obj in objects.items() if owner in control_deps]
    seed_only = sorted((control_deps & seed_owners) - objects.keys())
    for owner in seed_only:
        obj = (stage / "original-native" / Path(*owner.split("."))).with_suffix(".o")
        inputs.append(compile_object((seed_files[owner], obj)))
    extra = []
    if check_mixed and all(modes.get(owner) == "mixed=" and owner in objects
           for owner in ("OmegaInit.Prelude", "OmegaInit.Control.Basic")):
        mixed = sources / "mixed-consumer.c"
        run("lean", "-R", STRICT_SOURCES, "-c", mixed, STRICT_SOURCES / "GeneratedMixedConsumer.lean",
            env={**os.environ, "LEAN_PATH": str(library)})
        extra = ["-DOMEGA_TEST_MIXED", mixed]
        if check_names and literals.is_file():
            names = sources / "name-scope-consumer.c"
            run("lean", "-R", STRICT_SOURCES, "-c", names, STRICT_SOURCES / "NameScopeConsumer.lean",
                env={**os.environ, "LEAN_PATH": str(library)})
            extra += ["-DOMEGA_TEST_NAMES", names]
    if literals.exists() and check_literals:
        client = sources / "literal-consumer.c"
        run("lean", "-R", STRICT_SOURCES, "-c", client, STRICT_SOURCES / "LiteralConsumer.lean",
            env={**os.environ, "LEAN_PATH": str(library)})
        extra += ["-DOMEGA_TEST_LITERALS", client]
    app = sources / "consumer"
    run("leanc", "-I", HERE, consumer, HERE / "consumers" / "generated_control_consumer.c", *extra, *inputs, "-o", app)
    run(app)
    return inputs
