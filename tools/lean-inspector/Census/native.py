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
    project = repository / ".lake/build/lib/lean"
    custom, seen, pending = [], set(), [source]
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        dependencies = subprocess.check_output(["lean", "--deps", str(current)],
                                               cwd=repository, env=env, text=True).splitlines()
        for name in dependencies:
            path = pathlib.Path(name).resolve()
            if path.is_relative_to(project):
                relative = path.relative_to(project)
                custom.append(repository / ".lake/build/ir" / relative.with_suffix(".c"))
                pending.append(repository / "tools/lean-inspector" / relative.with_suffix(".lean"))
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
