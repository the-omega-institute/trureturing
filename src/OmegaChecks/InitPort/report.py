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


def check_coverage(official):
    """Count physical sites from the fresh Lean inventory, including repeated names."""
    modules = set(official["modules"])
    sites = set()
    direct = 0
    matched = 0
    reductions = 0
    unresolved = []
    for row in official["declarations"]:
        owner, name = site = (row["module"], row["name"])
        if owner not in modules or site in sites:
            raise ValueError(f"invalid or repeated official definition site {owner}/{name}")
        sites.add(site)
        port = row["matchingNameAndModule"]
        axiom = row["kind"] == "axiom"
        witness, target = row["reductionWitness"], row["impliesAxiom"]
        if bool(witness) != bool(target):
            raise ValueError(f"incomplete axiom reduction for {owner}/{name}")
        runtime = row.get("runtimeConflictWitness")
        if runtime and (axiom or witness or not row.get("unsafe") or
                        row.get("logicalConsequence") != "False" or
                        row.get("logicalConsequenceWitness") != runtime or not row.get("requiredBehavior")):
            raise ValueError(f"inconsistent runtime conflict for {owner}/{name}")
        if port:
            if axiom or witness or runtime or row["strictModule"] != "Omega" + owner:
                raise ValueError(f"inconsistent strict match for {owner}/{name}")
            matched += 1
        elif axiom:
            direct += 1
        elif witness:
            reductions += 1
        elif not runtime:
            unresolved.append(site)
    summary = official["summary"]
    if (not sites or not modules or len(sites) != summary["declarations"] or
            matched != summary["matchingNameAndModule"] or direct != summary["directAxioms"]):
        raise ValueError("official inventory counts do not agree with its definition sites")
    return reductions, unresolved


def verify_complete(official, product, reductions, unresolved):
    if unresolved:
        examples = ", ".join(f"{owner}/{name}" for owner, name in unresolved[:3])
        runtime = sum(bool(row.get("runtimeConflictWitness")) for row in official["declarations"])
        raise ValueError(f"{len(unresolved)} unresolved public non-axiom definition sites; "
                         f"{reductions} checked axiom reductions, {runtime} observed runtime conflicts. "
                         f"Examples: {examples}. See init-gaps.tsv.")
    missing_native = [(row["module"], row["name"]) for row in official["declarations"]
                      if row["matchingNameAndModule"] and row.get("strictNativeSignature") is False]
    if missing_native:
        examples = ", ".join(f"{owner}/{name}" for owner, name in missing_native[:3])
        raise ValueError(f"{len(missing_native)} matched definitions lack their official native signatures. "
                         f"Examples: {examples}. See init-inventory.json.")
    # Never accept an old audit log or a same-name strict declaration as a certificate.
    # Audit the product actually being presented, against all installed official module roots.
    lib = product / "lib"
    roots = ["Omega" + module for module in official["modules"]]
    subprocess.run(["lake", "build", "omegaAudit", "+OmegaChecks.Interface.Equations"], cwd=ROOT, check=True)
    subprocess.run(["lake", "env", "lean", "--run", HERE / "ExportAxioms.lean", "--check", lib, *roots],
                   cwd=ROOT, check=True)
    subprocess.run(["lake", "env", ROOT / ".lake/build/bin/omegaAudit",
                    "--exact-roots", lib, *roots, "--", *roots], cwd=ROOT, check=True)


def report(product, require_complete=False):
    with tempfile.TemporaryDirectory(dir=product) as work:
        stage = Path(work)
        inventory = stage / "init-inventory.json"
        subprocess.run(["lake", "build", "+OmegaChecks.InitInventory"], cwd=ROOT, check=True)
        subprocess.run(["lake", "env", "lean", "--run", HERE.parent / "InitInventory.lean", product / "lib", inventory],
                       cwd=ROOT, check=True)
        official = json.loads(inventory.read_text())
        reduction_count, unresolved = check_coverage(official)
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
                             "impliesAxiom", "firstDependencyPath", "reason", "reductionWitness",
                             "logicalConsequence", "logicalConsequenceWitness", "requiredBehavior", "abstractedDependency",
                             "runtimeConflictWitness", "equationOperand", "operandImpliesAxiom", "operandReductionWitness",
                             "unchangedTypeAxioms"])
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
                                 " -> ".join(path), " ".join(reason.splitlines()), row["reductionWitness"],
                                 row.get("logicalConsequence"), row.get("logicalConsequenceWitness"),
                                 row.get("requiredBehavior"), row.get("abstractedDependency"), row.get("runtimeConflictWitness"),
                                 row.get("equationOperand"), row.get("operandImpliesAxiom"), row.get("operandReductionWitness"),
                                 ",".join(row.get("unchangedTypeAxioms", []))])
        reductions = stage / "init-public-reductions.tsv"
        with reductions.open("w", newline="") as f:
            writer = csv.writer(f, delimiter="\t", lineterminator="\n")
            writer.writerow(["module", "declaration", "sealedDefinition", "strictDependencyPath",
                             "officialReductionMechanism"])
            for row in official["declarations"]:
                path = row["publicReductionBoundary"]
                if path:
                    writer.writerow([row["module"], row["name"], path[-1], " -> ".join(path),
                                     row["officialReductionMechanism"]])
        reductions.replace(product / reductions.name)
        inventory.replace(product / inventory.name)
        output.replace(product / output.name)
    if require_complete:
        verify_complete(official, product, reduction_count, unresolved)


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("product", type=Path, help="audited output from build.py")
    cli.add_argument("--require-complete", action="store_true",
                     help="require an implementation, checked axiom reduction or observed runtime contradiction for every site")
    args = cli.parse_args()
    try:
        report(args.product.resolve(), require_complete=args.require_complete)
    except ValueError as error:
        cli.exit(1, f"{error}\n")
