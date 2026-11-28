"""Measure which imports expose a common complete type for slice and envelope propositions."""
from bisect import bisect_right
from collections import defaultdict
import json
import os
from pathlib import Path
import subprocess
import tempfile

import finite_consumers
import public_clients

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SLICE_MODULES = {"Init.Data.Slice.Array.Lemmas", "Init.Data.Slice.List.Lemmas",
                 "Init.Data.Slice.InternalLemmas", "Init.Data.Slice.Lemmas"}
MODULES = SLICE_MODULES | {"Init.Grind.Module.Envelope"}


def scopes(checks):
    result = {}
    for owner, name, mode in checks:
        if owner not in MODULES or mode not in {"ordinary", "all"} or (owner, name) in result:
            raise ValueError(f"invalid module-body conversion certificate at {owner}/{name}")
        result[owner, name] = mode
    return result


def candidates(rows):
    found = set()
    for row in rows:
        owner = row["module"]
        gap = row.get("originalTypeGap") or ""
        if not row["matchingNameAndModule"] or row.get("originalTypeChecked") is not False or row["kind"] != "theorem":
            continue
        if ((owner in SLICE_MODULES and "The upstream public interface hides" in gap) or
                (owner == "Init.Grind.Module.Envelope" and "Public reduction of the pinned statement" in gap)):
            found.add((owner, row["name"]))
    return found


def _reject_ordinary(library, client, names, strict):
    env = dict(os.environ, LEAN_PATH=str(library)) if strict else os.environ
    result = subprocess.run(["lean", "--json", client], env=env, cwd=ROOT, capture_output=True, text=True)
    sections = [i for i, line in enumerate(client.read_text().splitlines(), 1) if line == "section"]
    errors = [row for line in result.stdout.splitlines() if (row := json.loads(line))["severity"] == "error"]
    rejected = {bisect_right(sections, row["pos"]["line"]) - 1 for row in errors}
    if not result.returncode or len(sections) != len(names) or rejected != set(range(len(names))):
        raise ValueError(f"ordinary import did not reject every corresponding client in {client.name}")


def certificates(product, rows):
    selected = candidates(rows)
    if not selected:
        return []
    grouped = defaultdict(list)
    for owner, name in sorted(finite_consumers.sites(selected)):
        grouped[owner].append(name)
    library = product / "lib"
    with tempfile.TemporaryDirectory(dir=product) as temp:
        for owner, names in grouped.items():
            directory = Path(temp) / owner
            directory.mkdir()
            (directory / "sites.txt").write_text("\n".join(names) + "\n")
        result = subprocess.run(["lake", "env", "lean", "--run", HERE / "ScopedConsumerCheck.lean", library, temp],
                                cwd=ROOT, capture_output=True, text=True)
        if result.returncode:
            raise ValueError(result.stderr + result.stdout)
        checks = sorted(json.loads(line) for line in result.stdout.splitlines())
        certified = scopes(checks)
        if not certified.keys() <= selected:
            raise ValueError("module-body evidence for a declaration outside the selected modules")
        by_import = defaultdict(set)
        for (owner, name), mode in certified.items():
            by_import[owner, mode].add(name)
        for (owner, mode), names in by_import.items():
            directory = Path(temp) / owner / mode
            public_clients.check(library, directory, names, "Changed")
            _reject_ordinary(library, directory / "OfficialOrdinary.lean", names, False)
            if mode == "all":
                _reject_ordinary(library, directory / "StrictOrdinary.lean", names, True)
        return checks
