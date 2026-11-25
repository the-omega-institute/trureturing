"""List the remaining public Init interfaces and their first observed porting dependency."""
import argparse
import csv
import json
from collections import defaultdict
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def report(product):
    with tempfile.TemporaryDirectory(dir=product) as work:
        stage = Path(work)
        inventory = stage / "init-inventory.json"
        subprocess.run(["lean", "--run", HERE.parent / "InitInventory.lean", product / "lib", inventory],
                       cwd=ROOT, check=True)
        official = json.loads(inventory.read_text())
        with (product / "inventory.jsonl").open() as f:
            attempts = {}
            owners = defaultdict(list)
            for owner, name, _, why, dep in map(json.loads, f):
                attempts[owner, name] = (why, dep)
                owners[name].append(owner)
        with (product / "interface-rejections.jsonl").open() as f:
            rejected = dict(map(json.loads, f))
        # Incompatible copies are rejected together. Transfer visits one active
        # name, while every physical Init definition site needs that explanation.
        conflicts = {n: [] for n, reason in rejected.items()
                     if reason.startswith("distinct official declarations under the same name")}
        for row in official["declarations"]:
            if row["name"] in conflicts:
                conflicts[row["name"]].append(row["module"])
        output = stage / "init-gaps.tsv"
        with output.open("w", newline="") as f:
            writer = csv.writer(f, delimiter="\t", lineterminator="\n")
            writer.writerow(["module", "declaration", "kind", "unsafe", "partial", "upstreamAxioms",
                             "impliesAxiom", "firstDependencyPath", "reason"])
            for row in official["declarations"]:
                if row["matchingNameAndModule"] or row["kind"] == "axiom":
                    continue
                name = row["name"]
                path = [name]
                key = (row["module"], name)
                if key in attempts:
                    why, dep = attempts[key]
                elif name in owners:
                    why, dep = "no candidate at this defining module (attempted in " + ", ".join(owners[name]) + ")", ""
                else:
                    why, dep = "outside selected roots", ""
                while dep and dep not in path:
                    path.append(dep)
                    dep_owners = owners.get(dep, [])
                    if len(dep_owners) != 1:
                        why = ("ambiguous candidate dependency owner" if dep_owners else
                               "dependency missing from candidate inventory")
                        dep = ""
                        break
                    key = (dep_owners[0], dep)
                    why, dep = attempts[key]
                reason = rejected.get(path[-1], why) if why == "no computation correspondence" else why
                if path[-1] in conflicts:
                    reason = (rejected[path[-1]] + ". Public Init definition sites: "
                              + ", ".join(sorted(conflicts[path[-1]])))
                if dep in path:
                    reason = f"dependency cycle through {dep}"
                writer.writerow([row["module"], name, row["kind"], str(row["unsafe"]).lower(),
                                 str(row["partial"]).lower(), ",".join(row["axioms"]), row["impliesAxiom"],
                                 " -> ".join(path), " ".join(reason.splitlines())])
        inventory.replace(product / inventory.name)
        output.replace(product / output.name)


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("product", type=Path, help="audited output from build.py")
    report(cli.parse_args().product.resolve())
