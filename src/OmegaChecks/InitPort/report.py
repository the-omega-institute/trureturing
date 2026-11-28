"""List the remaining public Init interfaces and their first observed porting dependency."""
import argparse
import csv
import json
import os
from collections import defaultdict
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
STRICT_SOURCES = ROOT / "strict/OmegaChecks/InitPort"


# The pinned specification sites use the selector in their predicate, while
# congruence rules take their names directly from the selected operation.
SELECTOR_SPECIFICATIONS = {
    ("Init.Classical", "Classical.choose_spec"): "Classical.choose",
    ("Init.Classical", "Exists.choose_spec"): "Exists.choose",
    ("Init.Classical", "Classical.epsilon_spec"): "Classical.epsilon",
    ("Init.Classical", "Classical.epsilon_spec_aux"): "Classical.epsilon",
}


UNSAFE_OBSERVERS = {
    ("Init.Util", "ptrAddrUnsafe"): "lean_ptr_addr",
    ("Init.Util", "isExclusiveUnsafe"): "lean_is_exclusive_obj",
    ("Init.ShareCommon", "ShareCommon.Object.eq"): "lean_sharecommon_eq",
    ("Init.ShareCommon", "ShareCommon.Object.hash"): "lean_sharecommon_hash",
}


ENVELOPE_COUNTEREXAMPLES = {
    ("Init.Grind.Ring.Envelope", "Lean.Grind.Ring.OfSemiring.neg_add_cancel"): "theorem",
    ("Init.Grind.Module.Envelope", "Lean.Grind.IntModule.OfNatModule.neg_add_cancel"): "theorem",
    ("Init.Grind.Ring.Envelope", "Lean.Grind.Ring.OfSemiring.ofSemiring"): "definition",
    ("Init.Grind.Ring.Envelope", "Lean.Grind.CommRing.OfCommSemiring.ofCommSemiring"): "definition",
    ("Init.Grind.Module.Envelope", "Lean.Grind.IntModule.OfNatModule.ofNatModule"): "definition",
    ("Init.Grind.Module.Envelope", "Lean.Grind.IntModule.OfNatModule.add_zsmul"): "theorem",
    ("Init.Grind.Module.Envelope", "Lean.Grind.IntModule.OfNatModule.instIsPartialOrderQ"): "theorem",
    ("Init.Grind.Module.Envelope", "Lean.Grind.IntModule.OfNatModule.instIsLinearOrderQ"): "theorem",
    ("Init.Grind.Ring.Envelope", "Lean.Grind.Ring.OfSemiring.add"): "definition",
    ("Init.Grind.Ring.Envelope", "Lean.Grind.Ring.OfSemiring.sub"): "definition",
    ("Init.Grind.Ring.Envelope", "Lean.Grind.Ring.OfSemiring.mul"): "definition",
    ("Init.Grind.Ring.Envelope", "Lean.Grind.Ring.OfSemiring.neg"): "definition",
    ("Init.Grind.Module.Envelope", "Lean.Grind.IntModule.OfNatModule.add"): "definition",
    ("Init.Grind.Module.Envelope", "Lean.Grind.IntModule.OfNatModule.sub"): "definition",
    ("Init.Grind.Module.Envelope", "Lean.Grind.IntModule.OfNatModule.neg"): "definition",
    ("Init.Grind.Ring.Envelope", "Lean.Grind.Ring.OfSemiring.add.eq_1"): "theorem",
    ("Init.Grind.Ring.Envelope", "Lean.Grind.Ring.OfSemiring.sub.eq_1"): "theorem",
    ("Init.Grind.Ring.Envelope", "Lean.Grind.Ring.OfSemiring.mul.eq_1"): "theorem",
    ("Init.Grind.Ring.Envelope", "Lean.Grind.Ring.OfSemiring.neg.eq_1"): "theorem",
}


EFFECT_RUNNERS = {("Init.System.IO", name) for name in ("unsafeBaseIO", "unsafeEIO", "unsafeIO")}


def check_coverage(official):
    """Count physical sites from the fresh Lean inventory, including repeated names."""
    modules = set(official["modules"])
    certificates = official.get("certifiedChoiceEndpoints", [])
    by_site = {(owner, name): (operand, witness) for owner, name, operand, witness in certificates}
    if len(by_site) != len(certificates):
        raise ValueError("repeated specialized equality endpoint certificate")
    arguments = official.get("certifiedFormationArguments", [])
    by_argument = {(owner, name): (arg, target, witness) for owner, name, arg, target, witness in arguments}
    if len(arguments) != len(by_argument):
        raise ValueError("repeated statement formation argument certificate")
    paths = official.get("certifiedTransportPaths", [])
    by_transport = {(owner, name): path for owner, name, path in paths}
    if len(paths) != len(by_transport):
        raise ValueError("repeated transport path certificate")
    models = official.get("certifiedRepresentativeRefutations", [])
    by_refutation = {(owner, name): (target, proof) for owner, name, target, proof in models}
    if len(models) != len(by_refutation):
        raise ValueError("repeated representative quotient counterexample")
    sites = set()
    direct = 0
    matched = 0
    original_types = 0
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
        strict = row.get("strictSelectionWitness")
        strict_target = row.get("strictImpliesAxiom")
        if bool(strict) != bool(strict_target) or (strict and (strict_target != "Classical.choice.{1}" or
                strict != "OmegaStrictReference." + name or axiom or port or witness)):
            raise ValueError(f"inconsistent strict choice reduction for {owner}/{name}")
        reduction_axiom = row.get("kernelReductionAxiom")
        if site == ("Init.Prelude", "unsafeCast"):
            if reduction_axiom != "lcProof" or port or axiom or not row.get("unsafe") or target != "sorryAx":
                raise ValueError("invalid pinned reduction boundary for unsafeCast")
        elif site == ("Init.ShareCommon", "ShareCommon.StateFactory.get"):
            if (reduction_axiom != "lcProof" or port or axiom or not row.get("unsafe")
                    or row.get("logicalConsequence") != "False"
                    or row.get("logicalConsequenceWitness") != "OmegaChecks.InitBoundaries.FactoryCarriers.noGetCast"):
                raise ValueError("invalid pinned reduction boundary for ShareCommon.StateFactory.get")
        elif owner == "Init.Data.ByteArray.Basic" and name in {"ByteArray.forInUnsafe.loop", "ByteArray.foldlMUnsafe.fold"}:
            law = "noForInBound" if name == "ByteArray.forInUnsafe.loop" else "noFoldBranchBound"
            if (reduction_axiom != "lcProof" or port or axiom or not row.get("unsafe")
                    or row.get("logicalConsequence") != "False"
                    or row.get("logicalConsequenceWitness") != "OmegaChecks.InitBoundaries.ByteArrayReads." + law):
                raise ValueError(f"invalid byte array read boundary for {name}")
        elif reduction_axiom:
            raise ValueError(f"unexpected kernel reduction axiom for {owner}/{name}")
        runtime = row.get("runtimeConflictWitness")
        endpoint = row.get("specializedEndpointType")
        certificate = by_site.pop(site, None)
        operand = row.get("equationOperand")
        evidence = (operand, row.get("operandReductionWitness"))
        if bool(endpoint) != bool(certificate) or (endpoint and certificate != evidence):
            raise ValueError(f"uncertified specialized equality endpoint for {owner}/{name}")
        if endpoint and (endpoint != "Classical.choice" or row["kind"] != "theorem" or
                         not operand or (name != f"{operand}.congr_simp" and
                         SELECTOR_SPECIFICATIONS.get(site) != operand) or
                         row.get("operandImpliesAxiom") != endpoint or not row.get("operandReductionWitness") or
                         port or witness or strict or runtime):
            raise ValueError(f"inconsistent specialized equality endpoint for {owner}/{name}")
        argument = row.get("formationArgument")
        formation = by_argument.pop(site, None)
        if bool(argument) != bool(formation) or (argument and formation !=
                (argument, row.get("logicalConsequence"), row.get("logicalConsequenceWitness"))):
            raise ValueError(f"uncertified statement formation argument for {owner}/{name}")
        if argument and (site != ("Init.Core", "Quot.liftIndepPr1") or argument != "Quot.indepCoherent" or
                         row["kind"] != "theorem" or row.get("logicalConsequence") != "Quot.sound" or
                         not row.get("requiredBehavior") or port or witness or strict or runtime or endpoint):
            raise ValueError(f"inconsistent statement formation argument for {owner}/{name}")
        path = row.get("transportPathType")
        if path != by_transport.pop(site, None):
            raise ValueError(f"uncertified transport path for {owner}/{name}")
        if path:
            carrier = name.split(".")[0]
            if (owner != "Init.Core" or carrier not in ("Quot", "Quotient") or
                    name not in (carrier + ".rec", carrier + ".recOn") or path != carrier + ".sound" or
                    row["kind"] != "definition" or port or witness or strict or runtime or endpoint or argument):
                raise ValueError(f"inconsistent transport path for {owner}/{name}")
        refuter = row.get("representativeRefuter")
        certified_model = by_refutation.pop(site, None)
        if bool(refuter) != bool(certified_model):
            raise ValueError(f"uncertified representative quotient counterexample for {owner}/{name}")
        if refuter:
            target = path or name
            decision = target == "Quotient.decidableEq"
            suffix = {"Quotient.sound": "refuteSound", "instSubsingletonSquash": "refuteSquash",
                      "Quotient.decidableEq": "refutePositiveDecision"}.get(target)
            expected_kind = "definition" if path or decision else "theorem"
            if site in ENVELOPE_COUNTEREXAMPLES:
                suffix = "refuteEnvelopeCancellation"
                expected_kind = ENVELOPE_COUNTEREXAMPLES[site]
            elif owner != "Init.Core":
                suffix = None
            if (not suffix or certified_model != (target, refuter) or
                    refuter != "OmegaChecks.InitBoundaries.RepresentativeQuotient." + suffix or
                    (path and path != "Quotient.sound") or row["kind"] != expected_kind or
                    (decision and (row.get("logicalConsequence") != "funext" or not row.get("requiredBehavior"))) or
                    row.get("unsafe") or row.get("partial") or port or witness or strict or runtime or endpoint or argument):
                raise ValueError(f"inconsistent representative quotient counterexample for {owner}/{name}")
        if runtime and (axiom or witness or not row.get("unsafe") or
                        row.get("logicalConsequence") != "False" or
                        row.get("logicalConsequenceWitness") != runtime or not row.get("requiredBehavior")):
            raise ValueError(f"inconsistent runtime conflict for {owner}/{name}")
        unsafe_runtime = row.get("checkedUnsafeRuntime")
        expected_runtime = UNSAFE_OBSERVERS.get(site) if port else None
        if unsafe_runtime != expected_runtime or (unsafe_runtime and
                (row["kind"] != "opaque" or not row.get("unsafe") or
                 (owner == "Init.Util" and not runtime))):
            raise ValueError(f"inconsistent checked unsafe runtime for {owner}/{name}")
        comparison = row.get("checkedPointerComparison", False)
        expected_comparison = port and site in {
            ("Init.Util", "ptrEq"), ("Init.Util", "withPtrEqUnsafe"), ("Init.Util", "ptrEqList"),
            ("Init.ShareCommon", "ShareCommon.Object.ptrEq")}
        if comparison is not expected_comparison or (comparison and
                (row["kind"] != "definition" or not row.get("unsafe") or not runtime)):
            raise ValueError(f"inconsistent checked pointer comparison for {owner}/{name}")
        callback = row.get("checkedAddressCallback", False)
        if callback is not (port and site == ("Init.Util", "withPtrAddrUnsafe")) or (callback and
                (row["kind"] != "definition" or not row.get("unsafe"))):
            raise ValueError(f"inconsistent checked address callback for {owner}/{name}")
        pointer_hash = row.get("checkedPointerHash", False)
        if pointer_hash is not (port and site == ("Init.ShareCommon", "ShareCommon.Object.ptrHash")) or (pointer_hash and
                (row["kind"] != "definition" or not row.get("unsafe") or not runtime)):
            raise ValueError(f"inconsistent checked pointer hash for {owner}/{name}")
        effect = row.get("checkedEffectRunner", False)
        if effect is not (port and site in EFFECT_RUNNERS) or (effect and
                (row["kind"] != "definition" or not row.get("unsafe") or not runtime)):
            raise ValueError(f"inconsistent checked effect runner for {owner}/{name}")
        if port:
            if axiom or witness or (runtime and not (unsafe_runtime or effect or comparison or pointer_hash)) or row["strictModule"] != "Omega" + owner:
                raise ValueError(f"inconsistent strict match for {owner}/{name}")
            matched += 1
            if official.get("schemaVersion", 0) >= 5:
                if row.get("originalTypeChecked") is True and row.get("originalTypeGap") is None:
                    original_types += 1
                elif row.get("originalTypeChecked") is False and row.get("originalTypeGap"):
                    unresolved.append(site)
                else:
                    raise ValueError(f"inconsistent original type check for {owner}/{name}")
        elif axiom:
            direct += 1
        elif (witness or strict) and not row.get("unsafe"):
            # These Lean reductions take a value usable by safe code. The kernel
            # prohibits supplying an unsafe implementation to such a witness.
            reductions += 1
        elif not endpoint and not argument and not refuter and path != "Quot.sound":
            unresolved.append(site)
    if by_refutation:
        raise ValueError("representative quotient counterexample has no definition site")
    if by_transport:
        raise ValueError("transport path certificate has no definition site")
    if by_argument:
        raise ValueError("statement formation argument certificate has no definition site")
    if by_site:
        raise ValueError("specialized equality endpoint certificate has no definition site")
    summary = official["summary"]
    if (not sites or not modules or len(sites) != summary["declarations"] or
            matched != summary["matchingNameAndModule"] or direct != summary["directAxioms"]):
        raise ValueError("official inventory counts do not agree with its definition sites")
    if official.get("schemaVersion", 0) >= 5 and summary.get("originalTypesChecked") != original_types:
        raise ValueError("original type count does not agree with the checked sites")
    return reductions, unresolved


def verify_complete(official, product, reductions, unresolved):
    if unresolved:
        examples = ", ".join(f"{owner}/{name}" for owner, name in unresolved[:3])
        runtime = sum(bool(row.get("runtimeConflictWitness")) and not row["matchingNameAndModule"]
                      for row in official["declarations"])
        endpoints = sum(bool(row.get("specializedEndpointType")) for row in official["declarations"])
        models = sum(bool(row.get("representativeRefuter")) for row in official["declarations"])
        formations = sum(bool(row.get("formationArgument")) or row.get("transportPathType") == "Quot.sound"
                         for row in official["declarations"])
        raise ValueError(f"{len(unresolved)} unresolved public non-axiom definition sites; "
                         f"{reductions} checked axiom reductions, {runtime} unmatched sites with observed conflicts for pure replacements, "
                         f"{endpoints} official statements with choice-valued equality endpoints, "
                         f"{formations} official statements requiring an axiom to supply a quotient argument, "
                         f"{models} statements, required paths or computations refuted in the representative quotient model. "
                         f"Examples: {examples}. See init-gaps.tsv.")
    if any(row["matchingNameAndModule"] and row.get("originalTypeChecked") is not True
           for row in official["declarations"]):
        raise ValueError("matched declarations require a fresh strict check of each original type")
    missing_native = [(row["module"], row["name"]) for row in official["declarations"]
                      if row["matchingNameAndModule"] and row.get("strictNativeSignature") is False]
    if missing_native:
        examples = ", ".join(f"{owner}/{name}" for owner, name in missing_native[:3])
        raise ValueError(f"{len(missing_native)} matched definitions lack their official native signatures. "
                         f"Examples: {examples}. See init-inventory.json.")
    safety_mismatches = [(row["module"], row["name"]) for row in official["declarations"]
                         if row["matchingNameAndModule"] and
                         (row.get("strictUnsafe") is not row["unsafe"] or row.get("strictPartial") is not row["partial"])]
    if safety_mismatches:
        examples = ", ".join(f"{owner}/{name}" for owner, name in safety_mismatches[:3])
        raise ValueError(f"{len(safety_mismatches)} matched definitions differ in safety or partiality. "
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


def check_strict_reference_choices(product, stage, attempts):
    owners = ["Init.System.ST", "Init.Control.StateRef", "Init.Internal.Order.Basic", "Init.Internal.Order.MonadTail"]
    promise_ctor = ("Init.System.Promise", "_private.Init.System.Promise.0.IO.Promise.mk")
    if attempts.get(promise_ctor, (None,))[0] in {"added", "existing"}:
        owners.append("Init.System.Promise")
    required = ("Void.mk", "ST.Prim.mkRef", "ST.Ref.ref", "ST.Out.val")
    if not all(attempts.get((owners[0], name), (None,))[0] in {"added", "existing"} for name in required):
        return {}
    lib = product / "lib"
    strict_owners = ("Omega" + owner for owner in owners)
    selected = [owner for owner in strict_owners if (lib / Path(*owner.split("."))).with_suffix(".olean").is_file()]
    subprocess.run(["lean", "-R", STRICT_SOURCES, "-o", stage / "StrictReferenceChoice.olean", STRICT_SOURCES / "StrictReferenceChoice.lean"],
                   cwd=ROOT, env={**os.environ, "LEAN_PATH": str(lib)}, check=True)
    if "OmegaInit.System.Promise" in selected:
        subprocess.run(["lean", "-R", STRICT_SOURCES, "-o", stage / "StrictPromiseChoice.olean", STRICT_SOURCES / "StrictPromiseChoice.lean"],
                       cwd=ROOT, env={**os.environ, "LEAN_PATH": os.pathsep.join(map(str, (stage, lib)))}, check=True)
    output = stage / "strict-reference-choice.json"
    subprocess.run(["lake", "env", "lean", "--run", HERE / "ReferenceChoiceCheck.lean", lib, stage, output, *selected],
                   cwd=ROOT, check=True)
    return {(owner, name): witness for owner, name, witness in json.loads(output.read_text())}


def check_strict_longest_matches(product, stage):
    lib = product / "lib"
    if not (lib / "OmegaInit/Data/String/Lemmas/Pattern/Basic.olean").is_file():
        return {}
    module = "StrictStringLongest"
    subprocess.run(["lean", "-R", STRICT_SOURCES, "-o", stage / f"{module}.olean", STRICT_SOURCES / f"{module}.lean"],
                   cwd=ROOT, env={**os.environ, "LEAN_PATH": str(lib)}, check=True)
    output = stage / "strict-longest-matches.json"
    subprocess.run(["lake", "env", "lean", "--run", HERE / "StringLongestCheck.lean", lib, stage, output],
                   cwd=ROOT, check=True)
    return {(owner, name): (target, witness) for owner, name, target, witness in json.loads(output.read_text())}


def check_strict_equivalences(product, stage):
    lib = product / "lib"
    owners = [f"Init.Data.Range.Polymorphic.{kind}Lemmas" for kind in ("Nat", "Int")
              if (lib / f"OmegaInit/Data/Range/Polymorphic/{kind}Lemmas.olean").is_file()]
    if (lib / "OmegaInit/Omega/Constraint.olean").is_file():
        owners.append("Init.Omega.Constraint")
    if (lib / "OmegaInit/Control/Lawful/MonadAttach/Lemmas.olean").is_file():
        owners.append("Init.Control.Lawful.MonadAttach.Lemmas")
    for owner in ("Init.Grind.Order", "Init.Grind.Ordered.Linarith", "Init.Grind.Ring.CommSolver", "Init.Data.Sum.Lemmas"):
        if (lib / Path(*("Omega" + owner).split("."))).with_suffix(".olean").is_file():
            owners.append(owner)
    if not owners:
        return {}
    output = stage / "strict-range-index.json"
    subprocess.run(["lake", "env", "lean", "--run", HERE / "RangeIndexCheck.lean", lib, output, *owners],
                   cwd=ROOT, check=True)
    return {(owner, name): (condition, proof) for owner, name, condition, proof in json.loads(output.read_text())}


def check_strict_fin_folds(product, stage):
    lib = product / "lib"
    if not (lib / "OmegaInit/Data/Fin/Fold.olean").is_file():
        return {}
    output = stage / "strict-fin-folds.json"
    subprocess.run(["lake", "env", "lean", "--run", HERE / "FinFoldCheck.lean", lib, output], cwd=ROOT, check=True)
    return {(owner, name): (condition, proof) for owner, name, condition, proof in json.loads(output.read_text())}


def report(product, require_complete=False):
    with tempfile.TemporaryDirectory(dir=product) as work:
        stage = Path(work)
        inventory = stage / "init-inventory.json"
        subprocess.run(["lake", "build", "+OmegaChecks.InitInventory", "+OmegaChecks.InitPort.Translation",
                        "+OmegaChecks.InitPort.StrictReplay", "+OmegaChecks.InitPort.Alternatives.InternalOrder"], cwd=ROOT, check=True)
        subprocess.run(["lake", "env", "lean", "--run", HERE.parent / "InitInventory.lean", product / "lib", inventory],
                       cwd=ROOT, check=True)
        official = json.loads(inventory.read_text())
        with (product / "inventory.jsonl").open() as f:
            attempts = {}
            owners = defaultdict(list)
            for owner, name, _, why, dep in map(json.loads, f):
                attempts[owner, name] = (why, dep)
                owners[name].append(owner)
        strict_choices = check_strict_reference_choices(product, stage, attempts)
        strict_matches = check_strict_longest_matches(product, stage)
        strict_folds = check_strict_fin_folds(product, stage)
        strict_equivalences = check_strict_equivalences(product, stage)
        admissibility = ("Init.Internal.Order.Basic", "Lean.Order.admissible")
        if attempts.get(admissibility, (None,))[0] in {"added", "existing"}:
            subprocess.run(["lake", "env", "lean", "--run", HERE / "AdmissibilityCheck.lean", product / "lib"],
                           cwd=ROOT, check=True)
        pending = {site: (*result, "strictLogicalConsequenceWitness")
                   for site, result in (strict_matches | strict_folds).items()}
        pending.update({site: (*result, "strictEquivalenceWitness") for site, result in strict_equivalences.items()})
        for row in official["declarations"]:
            site = (row["module"], row["name"])
            witness = strict_choices.get(site)
            if witness:
                row["strictSelectionWitness"] = witness
                row["strictImpliesAxiom"] = "Classical.choice.{1}"
            if consequence := pending.pop(site, None):
                target, proof, column = consequence
                if (row.get("logicalConsequence") != target or row["kind"] != "theorem" or
                        (row.get("requiredBehavior") and site not in strict_folds)):
                    raise ValueError(f"official logical consequence differs from strict proof for {site}")
                row["strictLogicalConsequence"] = target
                row[column] = proof
        if pending:
            raise ValueError(f"missing official definition sites for strict consequences: {sorted(pending)}")
        reduction_count, unresolved = check_coverage(official)
        if strict_choices or strict_matches or strict_equivalences or strict_folds:
            inventory.write_text(json.dumps(official, ensure_ascii=False, separators=(",", ":")) + "\n")
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
                             "unchangedTypeAxioms", "unsafePackedObservation", "strictImpliesAxiom", "strictSelectionWitness",
                             "unconditionalLogicalConsequence", "unconditionalLogicalConsequenceWitness",
                             "specializedEndpointType", "strictConstructorIff", "formationArgument", "transportPathType",
                             "strictLogicalConsequence", "strictLogicalConsequenceWitness", "strictEquivalenceWitness",
                             "representativeRefuter", "refinedQuotientConsequence", "originalTypeGap"])
            for row in official["declarations"]:
                if row["originalTypeChecked"] or row["kind"] == "axiom":
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
                if row["matchingNameAndModule"]:
                    reason = row["originalTypeGap"]
                writer.writerow([row["module"], name, row["kind"], str(row["unsafe"]).lower(),
                                 str(row["partial"]).lower(), ",".join(row["axioms"]), row["impliesAxiom"],
                                 " -> ".join(path), " ".join(reason.splitlines()), row["reductionWitness"],
                                 row.get("logicalConsequence"), row.get("logicalConsequenceWitness"),
                                 row.get("requiredBehavior"), row.get("abstractedDependency"), row.get("runtimeConflictWitness"),
                                 row.get("equationOperand"), row.get("operandImpliesAxiom"), row.get("operandReductionWitness"),
                                 ",".join(row.get("unchangedTypeAxioms", [])), row.get("unsafePackedObservation"),
                                 row.get("strictImpliesAxiom"), row.get("strictSelectionWitness"),
                                 row.get("unconditionalLogicalConsequence"), row.get("unconditionalLogicalConsequenceWitness"),
                                 row.get("specializedEndpointType"), "true" if row.get("strictConstructorIff") else "",
                                 row.get("formationArgument"), row.get("transportPathType"),
                                 row.get("strictLogicalConsequence"), row.get("strictLogicalConsequenceWitness"),
                                 row.get("strictEquivalenceWitness"), row.get("representativeRefuter"),
                                 row.get("refinedQuotientConsequence"), row.get("originalTypeGap")])
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
                     help="require an implementation or unconditional logical boundary for every site")
    args = cli.parse_args()
    try:
        report(args.product.resolve(), require_complete=args.require_complete)
    except ValueError as error:
        cli.exit(1, f"{error}\n")
