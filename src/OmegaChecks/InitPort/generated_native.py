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
    run("lean", "-R", HERE, "-o", check / (consumer + "Consumer.olean"), HERE / (consumer + "Consumer.lean"),
        env={**os.environ, "LEAN_PATH": str(library)})
    run("lake", "env", "lean", "--load-dynlib=" + str(shim), "--run", HERE / (consumer + "IRConsumer.lean"),
        library, check)


def compile_generated(stage, product, graph, seed_ir, owners=None, *, original_seed=None, before_owner=None):
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
    requests = [modes.get(owner, "") + owner for owner in selected]
    if owners is not None and "OmegaInit.Control.State" in requested and "OmegaInit.Control.Basic" not in requested:
        requests.insert(0, "layouts=OmegaInit.Control.Basic")
    env = {**os.environ, "LEAN_ABORT_ON_PANIC": "1"}
    callbacks = before_owner or {}
    literals = stage / "literal.c"
    if "OmegaInit.Prelude" in selected and modes.get("OmegaInit.Prelude") == "mixed=":
        run("lake", "env", "lean", "--run", HERE / "LiteralNative.lean", library, literals, env=env)
        if literals.exists():
            compile_object((literals, product / "native/literal.o"))
    pending = []

    def flush():
        if pending:
            run("lake", "env", "lean", "--run", HERE / "GeneratedNative.lean",
                library, sources, *pending, env=env)
            pending.clear()

    for request in requests:
        callback = callbacks.get(request.split("=")[-1])
        if callback:
            flush()
            callback()
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
            parts = [seed_files[owner]]
            if adapter := adapters.get(init_suffix(source)):
                adapter_source, obj = adapter
                parts.append(adapter_source)
            parts.append(source)
            obj = link_owner(obj, stage / "mixed-native" / owner, parts)
        else:
            compile_object((source, obj))
        return owner, obj

    with ThreadPoolExecutor(max_workers=4) as pool:
        objects = dict(pool.map(compile_owner, sorted(sources.rglob("*.c"))))
    if not set(CONTROL).issubset(selected):
        return []

    reachable = set()
    pending = list(CONTROL)
    while pending:
        owner = pending.pop()
        if owner in reachable:
            continue
        reachable.add(owner)
        pending.extend(graph.get(owner, ()))
    sources.mkdir(exist_ok=True, parents=True)
    consumer = sources / "consumer.c"
    run("lean", "-R", HERE, "-o", sources / "GeneratedControlConsumer.olean", "-c", consumer,
        HERE / "GeneratedControlConsumer.lean", env={**os.environ, "LEAN_PATH": str(library)})
    missing = sorted(owner for owner in reachable & seed_owners if not seed_files[owner].is_file())
    if missing:
        run("lake", "env", "lean", "--run", HERE / "GeneratedNative.lean", "--check-control", library, sources,
            env=env)
        print("Checked generated control consumers using packaged IR. Seed C files unavailable for "
              + ", ".join(missing), flush=True)
        return None
    inputs = [obj for owner, obj in objects.items() if owner in reachable]
    seed_only = sorted((reachable & seed_owners) - objects.keys())
    for owner in seed_only:
        obj = (stage / "original-native" / Path(*owner.split("."))).with_suffix(".o")
        inputs.append(compile_object((seed_files[owner], obj)))
    extra = []
    if all(modes.get(owner) == "mixed=" and owner in objects
           for owner in ("OmegaInit.Prelude", "OmegaInit.Control.Basic")):
        mixed = sources / "mixed-consumer.c"
        run("lean", "-R", HERE, "-c", mixed, HERE / "GeneratedMixedConsumer.lean",
            env={**os.environ, "LEAN_PATH": str(library)})
        extra = ["-DOMEGA_TEST_MIXED", mixed]
    if literals.exists():
        client = sources / "literal-consumer.c"
        run("lean", "-R", HERE, "-c", client, HERE / "LiteralConsumer.lean",
            env={**os.environ, "LEAN_PATH": str(library)})
        extra += ["-DOMEGA_TEST_LITERALS", client]
    app = sources / "consumer"
    run("leanc", consumer, HERE / "generated_control_consumer.c", *extra, *inputs, "-o", app)
    run(app)
    return inputs
