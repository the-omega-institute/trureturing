"""Compile checked definitions in generated Init owners and link an ordinary C consumer."""
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
CONTROL = ("OmegaInit.Control.Except", "OmegaInit.Control.Option", "OmegaInit.Control.State")


def run(*args, **options):
    subprocess.run(args, check=True, cwd=ROOT, **options)


def compile_generated(stage, product, graph, seed_ir, owners=CONTROL):
    """Add fresh owner objects to the staged product. Seed objects keep their existing owners."""
    requested = set(owners).intersection(graph)
    if not requested:
        return []
    selected = [owner for owner in graph if owner in requested]
    sources = stage / "generated-native"
    library = product / "lib"
    requests = ["layouts=OmegaInit.Control.Basic"] if "OmegaInit.Control.State" in requested else []
    run("lake", "env", "lean", "--run", HERE / "GeneratedNative.lean",
        library, sources, *requests, *selected)
    objects = []
    for owner in selected:
        path = Path(*owner.split("."))
        obj = (product / "native" / "generated" / path).with_suffix(".o")
        obj.parent.mkdir(exist_ok=True, parents=True)
        run("leanc", "-DLEAN_EXPORTING", "-c", (sources / path).with_suffix(".c"), "-o", obj)
        objects.append(obj)

    if not set(CONTROL).issubset(requested):
        return []
    reachable = set()
    pending = list(CONTROL)
    while pending:
        owner = pending.pop()
        if owner in reachable:
            continue
        reachable.add(owner)
        pending.extend(graph.get(owner, ()))
    for owner in sorted(reachable - requested):
        path = Path(*owner.split("."))
        src = (seed_ir / path).with_suffix(".c")
        if src.is_file():
            obj = (sources / "seed" / path).with_suffix(".o")
            obj.parent.mkdir(exist_ok=True, parents=True)
            run("leanc", "-DLEAN_EXPORTING", "-c", src, "-o", obj)
            objects.append(obj)

    consumer = sources / "consumer.c"
    run("lean", "-R", HERE, "-c", consumer, HERE / "GeneratedControlConsumer.lean",
        env={**os.environ, "LEAN_PATH": str(library)})
    app = sources / "consumer"
    run("leanc", consumer, HERE / "generated_control_consumer.c", *objects, "-o", app)
    run(app)
    return objects
