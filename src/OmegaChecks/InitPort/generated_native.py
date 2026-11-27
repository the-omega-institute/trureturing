"""Compile checked definitions in generated Init owners and link an ordinary C consumer."""
from concurrent.futures import ThreadPoolExecutor
from filecmp import cmp
from graphlib import TopologicalSorter
import os
from pathlib import Path
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
    run("leanc", "-DLEAN_EXPORTING", "-c", source, "-o", obj)
    return obj


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
    requests = [("layouts=" if owner in seed_owners else "") + owner for owner in selected]
    if owners is not None and "OmegaInit.Control.State" in requested and "OmegaInit.Control.Basic" not in requested:
        requests.insert(0, "layouts=OmegaInit.Control.Basic")
    env = {**os.environ, "LEAN_ABORT_ON_PANIC": "1"}
    callbacks = before_owner or {}
    pending = []

    def flush():
        if pending:
            run("lake", "env", "lean", "--run", HERE / "GeneratedNative.lean",
                library, sources, *pending, env=env)
            pending.clear()

    for request in requests:
        callback = callbacks.get(request.removeprefix("layouts="))
        if callback:
            flush()
            callback()
        pending.append(request)
        if len(pending) == 32:
            flush()
    flush()

    units = [(c, (product / "native" / "generated" / c.relative_to(sources)).with_suffix(".o"))
             for c in sorted(sources.rglob("*.c"))]
    with ThreadPoolExecutor(max_workers=4) as pool:
        list(pool.map(compile_object, units))
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
    if original_seed is not None:
        for owner in reachable & seed_owners:
            if not seed_files[owner].is_file():
                cached = match_cached_seed(owner, original_seed)
                if cached is not None:
                    seed_files[owner] = cached
    missing = sorted(owner for owner in reachable & seed_owners if not seed_files[owner].is_file())
    if missing:
        run("lake", "env", "lean", "--run", HERE / "GeneratedNative.lean", "--check-control", library, sources,
            env=env)
        print("Checked generated control consumers using packaged IR. Seed C files unavailable for "
              + ", ".join(missing), flush=True)
        return None
    # The strict seed already owns its native symbols. Its objects are link inputs for
    # this ordinary consumer and are supplied by the original strict library at deployment.
    seed_units = [(source, (sources / "seed" / Path(*owner.split("."))).with_suffix(".o"))
                  for owner, source in sorted(seed_files.items()) if owner in reachable & seed_owners and source.is_file()]
    with ThreadPoolExecutor(max_workers=4) as pool:
        seed_objects = list(pool.map(compile_object, seed_units))
    generated = [obj for source, obj in units if ".".join(source.relative_to(sources).with_suffix("").parts) in reachable]

    app = sources / "consumer"
    run("leanc", consumer, HERE / "generated_control_consumer.c", *generated, *seed_objects, "-o", app)
    run(app)
    return [*generated, *seed_objects]
