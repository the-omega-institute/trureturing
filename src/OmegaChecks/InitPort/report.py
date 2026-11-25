"""List the remaining public Init interfaces and their first observed porting dependency."""
import argparse
import csv
import json
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
            attempts = {n: (why, dep) for _, n, _, why, dep in map(json.loads, f)}
        with (product / "interface-rejections.jsonl").open() as f:
            rejected = dict(map(json.loads, f))
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
                why, dep = attempts.get(name, ("outside selected roots", ""))
                while dep and dep not in path:
                    path.append(dep)
                    why, dep = attempts.get(dep, ("dependency missing from candidate inventory", ""))
                reason = rejected.get(path[-1], why)
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
