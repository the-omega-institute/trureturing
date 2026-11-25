"""Compare the mathematical objects in affected D5 signatures at a protected revision."""
from collections import defaultdict
import json
import os
from pathlib import Path
import subprocess
import tempfile

from portable import ROOT, consumers, root


def module_name(path):
    if not path.endswith(".lean"):
        return None
    return path.removeprefix("src/").removeprefix("strict/").removesuffix(".lean").replace("/", ".")


def import_graph(repository, paths):
    files = [file for file in paths if module_name(file)]
    graph = defaultdict(set)
    for offset in range(0, len(files), 2048):
        batch = files[offset:offset + 2048]
        rows = json.loads(subprocess.check_output(["lean", "--deps-json", "--stdin"], cwd=repository,
                          input="".join(path + "\n" for path in batch), text=True))["imports"]
        for path, row in zip(batch, rows, strict=True):
            if row["errors"]:
                raise RuntimeError(f"{path}: {row['errors']}")
            graph[module_name(path)].update(entry["module"] for entry in row["result"]["imports"])
    return graph


def affected(old, new, changed):
    # Carry both sides' reverse edges, including a consumer losing its last Omega import.
    reverse = defaultdict(set)
    for graph in (old, new):
        for module, imports in graph.items():
            for dep in imports:
                reverse[dep].add(module)
    pending = list(changed)
    seen = set(changed)
    while pending:
        dependents = reverse[pending.pop()] - seen
        seen.update(dependents)
        pending.extend(dependents)
    portable = set(consumers(old)) | set(consumers(new))
    return sorted(name for name in old if root(name) == "D5" and name in seen and name in portable)


def targets(commit, before):
    def paths(*args):
        return subprocess.check_output(["git", *args], cwd=ROOT, text=True).split("\0")[:-1]

    directories = ["D5", "src", "strict", "Trureturing.lean"]
    modified = paths("diff", "--no-renames", "--name-only", "-z", commit, "--", *directories)
    new_files = paths("ls-files", "--others", "--exclude-standard", "-z", "--", *directories)
    changed = {module_name(p) for p in [*modified, *new_files] if module_name(p)}
    if not changed:
        return [], []
    old_files = paths("ls-tree", "-rz", "--name-only", commit, "--", *directories)
    present = paths("ls-files", "-co", "--exclude-standard", "-z", "--", *directories)
    old = import_graph(before, old_files)
    new = import_graph(ROOT, [p for p in present if (ROOT / p).is_file()])
    selected = affected(old, new, changed)
    return selected, [n for n in selected if n in new]


def compare(before, old_modules, new_modules, old_path, new_path):
    if not old_modules:
        return
    script = ROOT / "src/OmegaChecks/ProtectedUses.lean"
    with tempfile.TemporaryDirectory(prefix="omega-signatures-") as temp:
        request, output = (Path(temp) / name for name in ("request.json", "uses.json"))

        def snapshot(stage, modules, search, selected=None):
            request.write_text(json.dumps(dict(path=search, modules=modules, selected=selected)))
            subprocess.run(["lean", "--run", script, request, output], cwd=stage,
                           env={**os.environ, "LEAN_PATH": ""}, check=True)
            return json.loads(output.read_text())

        old = snapshot(before, old_modules, old_path)
        new = snapshot(ROOT, new_modules, new_path, [item["nameKey"] for item in old])
    current = {(d["module"], d["nameKey"]): {u["position"]: u for u in d["uses"]} for d in new}
    verified = 0
    for declaration in old:
        positions = current.get((declaration["module"], declaration["nameKey"]), {})
        for previous in declaration["uses"]:
            pos = previous["position"]
            actual = positions.get(pos, {})
            if (previous["objectKey"], previous["owner"]) != (actual.get("objectKey"), actual.get("owner")):
                raise ValueError(f"{declaration['module']} {declaration['name']} at {pos}: expected "
                                 f"{previous['object']} from {previous['owner']}, found "
                                 f"{actual.get('object', '<missing>')} from {actual.get('owner', '<missing>')}")
            verified += 1
    print(f"Verified {verified} protected Mathlib occurrences in {len(old_modules)} affected D5 modules.", flush=True)
