"""Build tiny native Lean IO entry points after the canonical warm Lake build."""

import hashlib
import pathlib
import subprocess

from incremental import atomic_json
from streaming import digest


def build(repository, program, env=None):
    repository = pathlib.Path(repository)
    source = repository / "tools/lean-inspector/Census" / program
    # Lean, not a copied import parser, supplies the complete dependency closure.
    project = repository.resolve() / ".lake/build"
    custom, seen, pending = [], set(), [source]
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        dependencies = subprocess.check_output(["lean", "--deps", str(current)],
                                               cwd=repository, env=env, text=True).splitlines()
        sources = subprocess.check_output(["lean", "--src-deps", str(current)],
                                          cwd=repository, env=env, text=True).splitlines()
        if len(dependencies) != len(sources):
            raise ValueError("Lean dependency source/artifact count mismatch")
        for name, source_name in zip(dependencies, sources):
            path = pathlib.Path(name).resolve()
            if path.is_relative_to(project):
                owner, relative = str(path).rsplit("/lib/lean/", 1)
                custom.append(pathlib.Path(owner) / "ir" / pathlib.Path(relative).with_suffix(".c"))
                pending.append(pathlib.Path(source_name).resolve())
    inputs = [source, *sorted(set(custom))]
    address = digest([(str(p.relative_to(repository)), hashlib.sha256(p.read_bytes()).hexdigest()) for p in inputs]
                     + [("toolchain", (repository / "lean-toolchain").read_text())])
    folder = repository / ".lake/build/census/native" / address[7:]
    binary = folder / source.stem
    if binary.is_file():
        return binary
    folder.mkdir(parents=True, exist_ok=True)
    generated = folder / (source.stem + ".c")
    subprocess.run(["lean", "-DmaxRecDepth=100000", "-c", str(generated), str(source)],
                   cwd=repository, env=env, check=True)
    subprocess.run(["leanc", "-O2", "-o", str(binary), str(generated), *map(str, inputs[1:])],
                   cwd=repository, env=env, check=True)
    atomic_json(folder / "inputs.json", {"digest": address, "inputs": list(map(str, inputs))})
    return binary
