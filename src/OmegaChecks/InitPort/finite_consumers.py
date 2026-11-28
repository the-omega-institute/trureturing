"""Check full public types that use finite consumers or projections in both backends."""
from collections import defaultdict
import json
from pathlib import Path
import subprocess
import tempfile

import public_clients

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
DETAIL = ". The finite-iterator reformulation checks in both public kernels."


def candidates(rows, category="finite"):
    if category == "projection":
        return {(row["module"], row["name"]) for row in rows if row["matchingNameAndModule"] and
                row["kind"] == "theorem" and row.get("originalTypeChecked") is False and
                (row.get("originalTypeGap") or "").endswith(". A definitionally equal reformulation checks in the public kernels.") and
                (row["module"] in {"Init.Grind.Ring.Envelope", "Init.Grind.Ring.CommSemiringAdapter"} or
                 (row["module"] == "Init.Internal.Order.Basic" and
                  "ImplicationOrder.instOrder" in row["originalTypeGap"].partition(". ")[0]))}
    return {(row["module"], row["name"]) for row in rows if row["matchingNameAndModule"] and
            row.get("originalTypeChecked") is False and (row.get("originalTypeGap") or "").endswith(DETAIL)}


def sites(checks):
    found = set()
    for owner, name in checks:
        if (not owner.startswith("Init.") or not all(part.isidentifier() for part in owner.split(".")) or
                not name or len(name.splitlines()) != 1 or (owner, name) in found):
            raise ValueError(f"invalid finite consumer public type certificate for {owner}/{name}")
        found.add((owner, name))
    return found


def certificates(product, rows, category="finite"):
    selected = candidates(rows, category)
    if not selected:
        return []
    grouped = defaultdict(list)
    for owner, name in sorted(sites(selected)):
        grouped[owner].append(name)
    with tempfile.TemporaryDirectory(dir=product) as temp:
        for owner, names in grouped.items():
            directory = Path(temp) / owner
            directory.mkdir()
            (directory / "sites.txt").write_text("\n".join(names) + "\n")
        library = product / "lib"
        result = subprocess.run(["lake", "env", "lean", "--run", HERE / "PublicConsumerCheck.lean", library, temp, category],
                                cwd=ROOT, stdout=subprocess.PIPE, text=True, check=True)
        checked = sorted(json.loads(line) for line in result.stdout.splitlines())
        if sites(checked) != selected:
            raise ValueError("public type evidence does not cover the requested definition sites")
        for owner, names in grouped.items():
            public_clients.check(library, Path(temp) / owner, set(names), "Changed")
        return checked
