"""List the remaining public Init interfaces and their first observed porting dependency."""
import argparse
import csv
import json
import os
from collections import defaultdict
from pathlib import Path
import subprocess
import tempfile

from choice_operands import CHOICE_TYPE_OPERANDS, choice_type_dependencies, specified_choice_sites
import fin_bounds
import finite_consumers
import order_consumers
import scoped_consumers

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

FORMATION_TARGETS = {
    ("Init.Core", "Quot.liftIndepPr1"): ("Quot.indepCoherent", "Quot.sound"),
    ("Init.Internal.Order.While", "Lean.Loop.forIn.eq_1"): ("Lean.Loop.forIn", "Classical.choice"),
}

FIX_FORMATIONS = {}
for arity in ("", "₂", "₃"):
    for base in ("extrinsicFix", "partialExtrinsicFix"):
        operator = "WellFounded." + base + arity
        suffixes = ["_eq_fix", "_eq_apply"]
        if operator == "WellFounded.extrinsicFix":
            suffixes.append("_invImage")
        if base == "partialExtrinsicFix":
            suffixes.append("_eq_apply_of_acc")
            if arity:
                suffixes.append("_eq_partialExtrinsicFix")
        for suffix in suffixes:
            site = ("Init.WFExtrinsicFix", operator + suffix)
            FIX_FORMATIONS[site] = (operator, "OmegaChecks.InitBoundaries.choiceFromFix" + arity)
            FORMATION_TARGETS[site] = (operator, "Classical.choice")


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
    ("Init.Grind.Ring.Envelope", "Lean.Grind.Ring.OfSemiring.add.eq_1"): "theorem",
    ("Init.Grind.Ring.Envelope", "Lean.Grind.Ring.OfSemiring.sub.eq_1"): "theorem",
    ("Init.Grind.Ring.Envelope", "Lean.Grind.Ring.OfSemiring.mul.eq_1"): "theorem",
    ("Init.Grind.Ring.Envelope", "Lean.Grind.Ring.OfSemiring.neg.eq_1"): "theorem",
}


EFFECT_RUNNERS = {("Init.System.IO", name) for name in ("unsafeBaseIO", "unsafeEIO", "unsafeIO")}


PROMISE_OWNER = "Init.System.Promise"
PROMISE_ELIMINATORS = {"IO.Promise.rec": "recursor", "IO.Promise.recOn": "definition", "IO.Promise.casesOn": "definition"}
PROMISE_TOKENS = ("_private.Init.System.Promise.0.IO.PromisePointed",
                  "_private.OmegaInit.System.Promise.0.Omega.IO.PromisePointed")


ORDER_OWNER = "Init.Internal.Order.Basic"
ORDER_PROOFS = {
    "Lean.Order.ImplicationOrder.instOrder": "OmegaChecks.InitBoundaries.InternalOrder.propextOfImplicationOrder",
    "Lean.Order.ReverseImplicationOrder.instOrder": "OmegaChecks.InitBoundaries.InternalOrder.propextOfReverseImplicationOrder",
}


def order_dependencies(certificates):
    dependencies = defaultdict(dict)
    for owner, name, dep, proof in certificates:
        site = (owner, name)
        if owner != ORDER_OWNER or ORDER_PROOFS.get(dep) != proof or dep in dependencies[site]:
            raise ValueError(f"invalid pinned implication order certificate for {site}")
        dependencies[site][dep] = proof
    return dependencies


def order_certificates(product):
    library = product / "lib"
    if not (library / "OmegaInit/Internal/Order/Basic.olean").is_file():
        return []
    result = subprocess.run(["lake", "env", "lean", "--run", HERE / "ImplicationOrderCheck.lean", library],
                            cwd=ROOT, stdout=subprocess.PIPE, text=True, check=True)
    return [json.loads(line) for line in result.stdout.splitlines()]


def choice_type_certificates(product):
    library = product / "lib"
    if not any((library / ("Omega" + owner.replace(".", "/") + ".olean")).is_file()
               for owner, _ in CHOICE_TYPE_OPERANDS):
        return []
    result = subprocess.run(["lake", "env", "lean", "--run", HERE / "ChoiceTypeDependencyCheck.lean", library],
                            cwd=ROOT, stdout=subprocess.PIPE, text=True, check=True)
    return [json.loads(line) for line in result.stdout.splitlines()]


MODULE_ENVELOPE = "Init.Grind.Module.Envelope"
ENVELOPE_INSTANCE = "Lean.Grind.IntModule.OfNatModule.ofNatModule"
ENVELOPE_REFUTER = "OmegaChecks.InitBoundaries.RepresentativeQuotient.refuteEnvelopeCancellation"
EMBEDDINGS = {ENVELOPE_INSTANCE.rsplit(".", 1)[0] + "." + name for name in ("toQ_add", "toQ_smul", "toQ_zero")}
MODULE_CONGRUENCES = "Init.Grind.Module.OfNatModule"
EMBEDDING_CONGRUENCES = {ENVELOPE_INSTANCE.rsplit(".", 1)[0] + "." + name for name in ("add_congr", "smul_congr")}


RING_ENVELOPE = "Init.Grind.Ring.Envelope"
RING_PREFIX = "Lean.Grind.Ring.OfSemiring."
RING_INSTANCE = RING_PREFIX + "ofSemiring"
RING_INSTANCE_SITES = {RING_PREFIX + name for name in (
    "toQ_natCast", "toQ_pow", "instNoNatZeroDivisorsQOfAddRightCancel", "instIsCharPQOfAddRightCancel")}


def envelope_instance_sites(checks, expected_owner, expected_names, expected_instance):
    sites = set()
    for owner, name, instance, refuter in checks:
        site = owner, name
        if (owner != expected_owner or name not in expected_names or instance != expected_instance or
                refuter != ENVELOPE_REFUTER or site in sites):
            raise ValueError(f"invalid envelope instance certificate for {site}")
        sites.add(site)
    return sites


SEMIRING_IMAGE_OWNER = "Init.Grind.Ring.CommSemiringAdapter"
SEMIRING_IMAGE_PREFIX = "Lean.Grind.CommRing.Expr.denoteSAsRing."
SEMIRING_IMAGE_RULES = {"eq_4": "addImage", "eq_5": "mulImage", "eq_6": "powImage", "eq_def": "casesEq"}


def semiring_image_sites(checks):
    sites = {}
    for owner, name, witness in checks:
        site = owner, name
        suffix = name.removeprefix(SEMIRING_IMAGE_PREFIX)
        if (site in sites or owner != SEMIRING_IMAGE_OWNER or not name.startswith(SEMIRING_IMAGE_PREFIX) or
                suffix not in SEMIRING_IMAGE_RULES or witness != "OmegaChecks.InitPort.SemiringImage." + SEMIRING_IMAGE_RULES[suffix]):
            raise ValueError(f"invalid semiring computation certificate for {site}")
        sites[site] = witness
    return sites


def envelope_type_dependencies(checks):
    embeddings = [row for row in checks if row[0] == MODULE_ENVELOPE]
    congruences = [row for row in checks if row[0] != MODULE_ENVELOPE]
    return (envelope_instance_sites(embeddings, MODULE_ENVELOPE, EMBEDDINGS, ENVELOPE_INSTANCE) |
            envelope_instance_sites(congruences, MODULE_CONGRUENCES, EMBEDDING_CONGRUENCES, ENVELOPE_INSTANCE))


def ring_instance_sites(checks):
    return envelope_instance_sites(checks, RING_ENVELOPE, RING_INSTANCE_SITES, RING_INSTANCE)


MODULE_ENVELOPE_PREFIX = ENVELOPE_INSTANCE.rsplit(".", 1)[0]
MODULE_LE = MODULE_ENVELOPE_PREFIX + ".instLEQOfOrderedAdd"
MODULE_LT = MODULE_ENVELOPE_PREFIX + ".instLTQOfOrderedAdd"
ORDER_COHERENCE = MODULE_LE + "._proof_3"
ORDER_WITNESSES = ("OmegaChecks.InitBoundaries.EnvelopeOrder.propextFromModuleLift",
                   "OmegaChecks.InitBoundaries.EnvelopeOrder.moduleLiftFromPropext")
ORDER_COMPARISONS = {MODULE_ENVELOPE_PREFIX + ".mk_le_mk": MODULE_LE,
                     MODULE_ENVELOPE_PREFIX + ".toQ_le": MODULE_LE, MODULE_ENVELOPE_PREFIX + ".toQ_lt": MODULE_LT}


def envelope_order_dependencies(checks):
    sites = {}
    for owner, name, instance, coherence, forward, reverse in checks:
        site = owner, name
        if (owner != MODULE_ENVELOPE or ORDER_COMPARISONS.get(name) != instance or
                coherence != ORDER_COHERENCE or (forward, reverse) != ORDER_WITNESSES or site in sites):
            raise ValueError(f"invalid public envelope order coherence for {site}")
        sites[site] = instance
    return sites


def envelope_type_certificates(product, *, order=False):
    library = product / "lib"
    if not (library / "OmegaInit/Grind/Module/Envelope.olean").is_file():
        return []
    result = subprocess.run(["lake", "env", "lean", "--run", HERE / "EnvelopeInstanceCheck.lean", library,
                             *(["order"] if order else [])],
                            cwd=ROOT, stdout=subprocess.PIPE, text=True, check=True)
    return [json.loads(line) for line in result.stdout.splitlines()]


def envelope_order_formations(checks):
    sites = {}
    witness = "OmegaChecks.InitBoundaries.EnvelopeOrder."
    for owner, name, order, coherence, forward, reverse, *construction in checks:
        if owner in (MODULE_ENVELOPE, MODULE_CONGRUENCES):
            scope, suffix, model = MODULE_ENVELOPE_PREFIX, "_proof_3", "Module"
        elif owner == "Init.Grind.Ring.Envelope":
            scope, suffix, model = "Lean.Grind.Ring.OfSemiring", "_proof_1", "Ring"
        else:
            raise ValueError(f"invalid quotient order owner {owner}")
        site = (owner, name)
        expected_construction = [witness + model.lower() + "OrderFromPropext"] if name == order else []
        names = ({scope + ".of_le", scope + ".of_not_le"} if owner == MODULE_CONGRUENCES else
                 {order, scope + ".instIsPreorderQ", scope + ".instOrderedAddQ"})
        expected_witnesses = (witness + "propextFrom" + model + "Lift", witness + model.lower() + "LiftFromPropext")
        if owner == MODULE_ENVELOPE and name == scope + ".instIsLinearPreorderQ":
            names.add(name)
            linear = "OmegaChecks.InitBoundaries.LinearEnvelopeOrder."
            expected_witnesses = linear + "propextFromLinearLift", linear + "linearLiftFromPropext"
        if (site in sites or name not in names or
                construction != expected_construction or order != scope + ".instLEQOfOrderedAdd" or coherence != order + "." + suffix or
                (forward, reverse) != expected_witnesses):
            raise ValueError(f"invalid quotient order formation dependency for {site}")
        sites[site] = order
    return sites


def envelope_formation_certificates(product, program="EnvelopeOrderFormation.lean"):
    result = subprocess.run(["lake", "env", "lean", "--run", HERE / program, product / "lib"],
                            cwd=ROOT, stdout=subprocess.PIPE, text=True, check=True)
    return [json.loads(line) for line in result.stdout.splitlines()]


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
    certificates = official.get("certifiedImportAllOriginalTypes", [])
    private_types = {(owner, name): (hidden, strict_hidden) for owner, name, hidden, strict_hidden in certificates}
    if len(private_types) != len(certificates):
        raise ValueError("repeated import all original type certificate")
    blocked_orders = order_dependencies(official.get("certifiedOrderTypeDependencies", []))
    choice_operands = choice_type_dependencies(official.get("certifiedChoiceTypeDependencies", []))
    embeddings = envelope_type_dependencies(official.get("certifiedEnvelopeTypeDependencies", []))
    if embeddings and by_refutation.get((MODULE_ENVELOPE, ENVELOPE_INSTANCE)) != (ENVELOPE_INSTANCE, ENVELOPE_REFUTER):
        raise ValueError("module embedding certificates lack the counterexample for their instance")
    image_sites = semiring_image_sites(official.get("certifiedSemiringEquations", []))
    specified = specified_choice_sites(official.get("certifiedSpecifiedChoice", []), official["declarations"])
    comparison_formations = envelope_order_formations(official.get("certifiedEnvelopeOrderFormations", []))
    ring_formations = ring_instance_sites(official.get("certifiedRingInstanceFormations", []))
    if ring_formations and by_refutation.get((RING_ENVELOPE, RING_INSTANCE)) != (RING_INSTANCE, ENVELOPE_REFUTER):
        raise ValueError("ring formation certificates lack the counterexample for their instance")
    comparisons = envelope_order_dependencies(official.get("certifiedEnvelopeOrderCoherence", []))
    finite_bounds = fin_bounds.sites(official.get("certifiedFinBoundTypes", []))
    pointwise_sites = order_consumers.sites(official.get("certifiedPointwiseOrderTypes", []))
    finite_sites = finite_consumers.sites(official.get("certifiedFiniteConsumerTypes", []))
    candidates = finite_consumers.candidates(official["declarations"])
    projections = finite_consumers.sites(official.get("certifiedProjectionTypes", []))
    projected_candidates = finite_consumers.candidates(official["declarations"], "projection")
    scopes = scoped_consumers.scopes(official.get("certifiedModuleBodyTypes", []))
    scoped_candidates = scoped_consumers.candidates(official["declarations"])
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
        if argument and (FORMATION_TARGETS.get(site) != (argument, row.get("logicalConsequence")) or
                         row["kind"] != "theorem" or row.get("unsafe") or row.get("partial") or
                         not row.get("requiredBehavior") or port or witness or strict or runtime or endpoint):
            raise ValueError(f"inconsistent statement formation argument for {owner}/{name}")
        if argument and site in FIX_FORMATIONS and (
                (argument, row.get("logicalConsequenceWitness")) != FIX_FORMATIONS[site] or
                (operand, row.get("operandReductionWitness")) != FIX_FORMATIONS[site] or
                row.get("operandImpliesAxiom") != "Classical.choice"):
            raise ValueError(f"incorrect unrestricted fixed-point formation argument for {owner}/{name}")
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
        private_type = row.get("importAllOriginalTypeChecked", False)
        tokens = private_types.pop(site, None)
        if private_type is not (tokens is not None) or (private_type and
                (owner != PROMISE_OWNER or name not in PROMISE_ELIMINATORS or row["kind"] != PROMISE_ELIMINATORS[name] or
                 not port or row.get("originalTypeChecked") is not False or tokens != PROMISE_TOKENS or
                 row.get("originalTypeGap") != f"missing type dependencies: {PROMISE_TOKENS[1]}" or
                 any(row.get(flag) is not False for flag in ("unsafe", "partial", "strictUnsafe", "strictPartial")))):
            raise ValueError(f"uncertified import all original type for {owner}/{name}")
        orders = blocked_orders.pop(site, {})
        if orders != row.get("originalTypeOrderDependencies", {}):
            raise ValueError(f"uncertified pinned order type dependency for {site}")
        if orders:
            gap = row.get("originalTypeGap") or ""
            missing = gap.partition(". ")[0].removeprefix("missing type dependencies: ").split(", ")
            if (not port or row["kind"] != "theorem" or row.get("originalTypeChecked") is not False or
                    any(row.get(flag) is not False for flag in ("unsafe", "partial", "strictUnsafe", "strictPartial")) or
                    private_type or any("Omega." + dep not in missing for dep in orders) or
                    not gap.endswith("A definitionally equal reformulation checks in the public kernels.")):
                raise ValueError(f"inconsistent pinned order type dependency for {site}")
        choice_operand = choice_operands.pop(site, None)
        if choice_operand != row.get("originalTypeChoiceDependency"):
            raise ValueError(f"uncertified choice operand of the pinned type for {site}")
        if choice_operand:
            expected_gap = f"missing type dependencies: Omega.{choice_operand}" if port else None
            expected_safety = False if port else None
            if (row["kind"] != "theorem" or row.get("originalTypeChecked") is not False or
                    row.get("originalTypeGap") != expected_gap or row["unsafe"] or row["partial"] or
                    any(row.get(flag) is not expected_safety for flag in ("strictUnsafe", "strictPartial")) or
                    private_type or orders):
                raise ValueError(f"uncertified choice operand of the pinned type for {site}")
        image = image_sites.get(site)
        if row.get("semiringImageEquation") != image or (image and (
                not port or row["kind"] != "theorem" or row.get("originalTypeChecked") is not False or
                (row.get("originalTypeGap") or "").partition(". ")[0] != "missing type dependencies: Omega." + RING_INSTANCE or
                any(row.get(flag) is not False for flag in ("unsafe", "partial", "strictUnsafe", "strictPartial")))):
            raise ValueError(f"uncertified semiring computation for {site}")
        selection = specified.pop(site, None)
        if (row.get("specifiedChoiceOperand"), row.get("specifiedChoiceObservation")) != (selection or (None, None)) or (
                selection and (port or row["kind"] != "theorem" or row["unsafe"] or row["partial"] or
                               row.get("originalTypeChecked") is not False or row.get("originalTypeGap") is not None)):
            raise ValueError(f"uncertified specified selector in {site}")
        embedding = site in embeddings
        embedding_gap = ("missing type dependencies: Omega." + ENVELOPE_INSTANCE) if port else ""
        if row.get("originalTypeEnvelopeInstance") != (ENVELOPE_INSTANCE if embedding else None) or (embedding and (
                port != (owner == MODULE_ENVELOPE) or row["kind"] != "theorem" or row.get("originalTypeChecked") is not False or
                (row.get("originalTypeGap") or "").partition(". ")[0] != embedding_gap or row["unsafe"] or row["partial"] or
                any(row.get(flag) is not (False if port else None) for flag in ("strictUnsafe", "strictPartial")))):
            raise ValueError(f"uncertified module instance in embedding equation {site}")
        order_formation = comparison_formations.get(site)
        if row.get("quotientOrderFormation") != order_formation or (order_formation and (
                port or row["kind"] not in ("theorem", "definition") or row["unsafe"] or row["partial"] or
                (order_formation == name and row["kind"] != "definition") or
                row.get("originalTypeChecked") is not False or row.get("originalTypeGap") is not None)):
            raise ValueError(f"uncertified public quotient order formation for {site}")
        ring_formation = site in ring_formations
        if row.get("quotientRingFormation") != (RING_INSTANCE if ring_formation else None) or (ring_formation and (
                port or row["kind"] != "theorem" or row["unsafe"] or row["partial"] or
                row.get("originalTypeChecked") is not False or row.get("originalTypeGap") is not None)):
            raise ValueError(f"uncertified public quotient ring formation for {site}")
        envelope_comparison = comparisons.get(site)
        if row.get("originalTypeEnvelopeOrderInstance") != envelope_comparison or (envelope_comparison and (
                not port or row["kind"] != "theorem" or row.get("originalTypeChecked") is not False or
                (row.get("originalTypeGap") or "").partition(". ")[0] != "missing type dependencies: Omega." + envelope_comparison or
                any(row.get(flag) is not False for flag in ("unsafe", "partial", "strictUnsafe", "strictPartial")))):
            raise ValueError(f"uncertified quotient comparison coherence for {site}")
        equivalent = site in finite_bounds
        if equivalent != row.get("finBoundProofReplacementChecked", False) or (equivalent and (
                not port or row["kind"] != "theorem" or row.get("originalTypeChecked") is not False or
                row.get("unchangedTypeAxioms") != ["propext"] or
                not (row.get("originalTypeGap") or "").endswith(". A definitionally equal reformulation checks in the public kernels.") or
                any(row.get(flag) is not False for flag in ("unsafe", "partial", "strictUnsafe", "strictPartial")) or
                private_type or orders or choice_operand)):
            raise ValueError(f"uncertified finite-index bound proof replacement for {site}")
        pointwise = site in pointwise_sites
        if pointwise != row.get("pointwiseOrderTypeChecked", False) or (pointwise and (
                not port or row["kind"] != "theorem" or row.get("originalTypeChecked") is not False or
                row.get("originalTypeGap") != order_consumers.gap(name) or
                any(row.get(flag) is not False for flag in ("unsafe", "partial", "strictUnsafe", "strictPartial")) or
                private_type or orders or equivalent or choice_operand)):
            raise ValueError(f"uncertified pointwise order proposition for {site}")
        finite = site in finite_sites
        if finite != row.get("finiteConsumerTypeChecked", False) or (finite and (
                site not in candidates or not port or row["kind"] not in {"theorem", "definition", "constructor", "recursor"} or
                any(row.get(flag) is not False for flag in ("unsafe", "partial", "strictUnsafe", "strictPartial")) or
                private_type or orders or equivalent or choice_operand or pointwise)):
            raise ValueError(f"uncertified finite consumer public type for {site}")
        projected = site in projections
        if projected != row.get("publicProjectionTypeChecked", False) or (projected and (
                site not in projected_candidates or not port or row["kind"] != "theorem" or
                any(row.get(flag) is not False for flag in ("unsafe", "partial", "strictUnsafe", "strictPartial")) or
                (owner == ORDER_OWNER and not orders) or private_type or equivalent or choice_operand or pointwise or finite)):
            raise ValueError(f"uncertified public projection proposition for {site}")
        scope = scopes.get(site)
        if row.get("moduleBodyStrictImport") != scope or (scope and (
                site not in scoped_candidates or row["kind"] != "theorem" or
                any(row.get(flag) is not False for flag in ("unsafe", "partial", "strictUnsafe", "strictPartial")) or
                private_type or equivalent or choice_operand or pointwise or finite or projected)):
            raise ValueError(f"uncertified module-body import requirement for {site}")
        if port:
            if axiom or witness or (runtime and not (unsafe_runtime or effect or comparison or pointer_hash)) or row["strictModule"] != "Omega" + owner:
                raise ValueError(f"inconsistent strict match for {owner}/{name}")
            matched += 1
            if official.get("schemaVersion", 0) >= 5:
                if row.get("originalTypeChecked") is True and row.get("originalTypeGap") is None:
                    original_types += 1
                elif row.get("originalTypeChecked") is False and row.get("originalTypeGap"):
                    if not any((private_type, choice_operand, equivalent, pointwise, finite, projected, embedding, envelope_comparison, image)):
                        unresolved.append(site)
                else:
                    raise ValueError(f"inconsistent original type check for {owner}/{name}")
        elif axiom:
            direct += 1
        elif (witness or strict) and not row.get("unsafe"):
            # These Lean reductions take a value usable by safe code. The kernel
            # prohibits supplying an unsafe implementation to such a witness.
            reductions += 1
        elif not any((selection, choice_operand, endpoint, argument, refuter, order_formation, ring_formation, embedding,
                      path == "Quot.sound")):
            unresolved.append(site)
    if not image_sites.keys() <= sites:
        raise ValueError("semiring computation certificate has no declaration")
    if specified:
        raise ValueError("specified selector certificate has no declaration")
    if not ring_formations <= sites:
        raise ValueError("ring formation certificate has no declaration")
    if not comparison_formations.keys() <= sites:
        raise ValueError("quotient order formation has no declaration")
    if not comparisons.keys() <= sites:
        raise ValueError("envelope order certificate has no definition site")
    if not embeddings <= sites:
        raise ValueError("module embedding certificate has no declaration")
    if not scopes.keys() <= sites:
        raise ValueError("module-body evidence has no definition site")
    if not projections <= sites:
        raise ValueError("public projection certificate has no definition site")
    if not finite_sites <= sites:
        raise ValueError("finite consumer certificate has no definition site")
    if not pointwise_sites <= sites:
        raise ValueError("pointwise order certificate has no definition site")
    if not finite_bounds <= sites:
        raise ValueError("finite-index bound certificate has no definition site")
    if choice_operands:
        raise ValueError("choice operand certificate has no definition site")
    if blocked_orders:
        raise ValueError("pinned order certificate has no definition site")
    if private_types:
        raise ValueError("import all original type certificate has no definition site")
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
    if summary.get("importAllOriginalTypesChecked", 0) != len(certificates):
        raise ValueError("import all original type count does not agree with the checked sites")
    if summary.get("finBoundProofReplacementsChecked", 0) != len(finite_bounds):
        raise ValueError("finite-index bound count does not agree with the checked sites")
    if summary.get("pointwiseOrderTypesChecked", 0) != len(pointwise_sites):
        raise ValueError("pointwise order count does not agree with the checked sites")
    if summary.get("finiteConsumerTypesChecked", 0) != len(finite_sites):
        raise ValueError("finite consumer count does not agree with the checked sites")
    if summary.get("publicProjectionTypesChecked", 0) != len(projections):
        raise ValueError("public projection count does not agree with the checked sites")
    if summary.get("moduleBodyTypesChecked", 0) != len(scopes):
        raise ValueError("module-body count does not agree with the checked sites")
    return reductions, unresolved


def coverage_totals(official, unresolved):
    """Partition non-axiom definition sites after check_coverage validates their certificates."""
    callable_sites = sum(
        any((row["originalTypeChecked"], row.get("importAllOriginalTypeChecked"),
             row.get("finBoundProofReplacementChecked"), row.get("pointwiseOrderTypeChecked"),
             row.get("finiteConsumerTypeChecked"), row.get("publicProjectionTypeChecked"),
             row.get("semiringImageEquation")))
        for row in official["declarations"] if row["kind"] != "axiom")
    non_axioms = official["summary"]["declarations"] - official["summary"]["directAxioms"]
    return {"publicNonAxioms": non_axioms, "callableAtOriginalType": callable_sites,
            "certifiedExceptions": non_axioms - callable_sites - len(unresolved), "unresolved": len(unresolved)}


def verify_complete(official, product, reductions, unresolved):
    if unresolved:
        examples = ", ".join(f"{owner}/{name}" for owner, name in unresolved[:3])
        runtime = sum(bool(row.get("runtimeConflictWitness")) and not row["matchingNameAndModule"]
                      for row in official["declarations"])
        endpoints = sum(bool(row.get("specializedEndpointType")) for row in official["declarations"])
        models = sum(bool(row.get("representativeRefuter")) for row in official["declarations"])
        embedding_types = len(official.get("certifiedEnvelopeTypeDependencies", []))
        formations = sum(bool(row.get("formationArgument")) or row.get("transportPathType") == "Quot.sound"
                         for row in official["declarations"])
        raise ValueError(f"{len(unresolved)} unresolved public non-axiom definition sites; "
                         f"{reductions} checked axiom reductions, {runtime} unmatched sites with observed conflicts for pure replacements, "
                         f"{endpoints} official statements with choice-valued equality endpoints, "
                         f"{formations} statements requiring an excluded axiom to form a faithful argument or endpoint, "
                         f"{models} statements, required paths or computations refuted in the representative quotient model, "
                         f"{embedding_types} embedding equations whose pinned instance is refuted in that model. "
                         f"Examples: {examples}. See init-gaps.tsv.")
    order_checks = official.get("certifiedOrderTypeDependencies", [])
    if order_checks and order_certificates(product) != order_checks:
        raise ValueError("live implication order certificates differ from inventory")
    choice_checks = official.get("certifiedChoiceTypeDependencies", [])
    if choice_checks and choice_type_certificates(product) != choice_checks:
        raise ValueError("live choice operand certificates differ from inventory")
    blocked = choice_type_dependencies(choice_checks).keys()
    embeddings = official.get("certifiedEnvelopeTypeDependencies", [])
    if embeddings and envelope_type_certificates(product) != embeddings:
        raise ValueError("live module embedding certificates differ from inventory")
    blocked = blocked | envelope_type_dependencies(embeddings)
    formations = official.get("certifiedEnvelopeOrderFormations", [])
    if formations and envelope_formation_certificates(product) != formations:
        raise ValueError("live quotient order formation certificates differ from inventory")
    image_checks = official.get("certifiedSemiringEquations", [])
    if image_checks and envelope_formation_certificates(product, "SemiringEquationsCheck.lean") != image_checks:
        raise ValueError("live semiring computation certificates differ from inventory")
    blocked = blocked | semiring_image_sites(image_checks).keys()
    specified = official.get("certifiedSpecifiedChoice", [])
    if specified and envelope_formation_certificates(product, "SpecifiedChoiceCheck.lean") != specified:
        raise ValueError("live specified selector certificates differ from inventory")
    ring_formations = official.get("certifiedRingInstanceFormations", [])
    if ring_formations and envelope_formation_certificates(product, "RingInstanceFormation.lean") != ring_formations:
        raise ValueError("live quotient ring formation certificates differ from inventory")
    comparisons = official.get("certifiedEnvelopeOrderCoherence", [])
    if comparisons and envelope_type_certificates(product, order=True) != comparisons:
        raise ValueError("live envelope order certificates differ from inventory")
    blocked = blocked | envelope_order_dependencies(comparisons).keys()
    bounds = official.get("certifiedFinBoundTypes", [])
    if bounds and fin_bounds.certificates(product) != bounds:
        raise ValueError("live finite-index bound certificates differ from inventory")
    pointwise = official.get("certifiedPointwiseOrderTypes", [])
    if pointwise and order_consumers.certificates(product) != pointwise:
        raise ValueError("live pointwise order certificates differ from inventory")
    finite = official.get("certifiedFiniteConsumerTypes", [])
    if finite and finite_consumers.certificates(product, official["declarations"]) != finite:
        raise ValueError("live finite consumer certificates differ from inventory")
    projections = official.get("certifiedProjectionTypes", [])
    if projections and finite_consumers.certificates(product, official["declarations"], "projection") != projections:
        raise ValueError("live public projection certificates differ from inventory")
    raw_type_alternatives = (blocked | fin_bounds.sites(bounds) | order_consumers.sites(pointwise) |
                             finite_consumers.sites(finite) | finite_consumers.sites(projections))
    certified = {(owner, name) for owner, name, _, _ in official.get("certifiedImportAllOriginalTypes", [])}
    if any(row["matchingNameAndModule"] and row.get("originalTypeChecked") is not True and
           (row["module"], row["name"]) not in raw_type_alternatives and
           (row.get("importAllOriginalTypeChecked") is not True or (row["module"], row["name"]) not in certified)
           for row in official["declarations"]):
        raise ValueError("matched declarations require a fresh strict check of each original type")
    if certified:
        if promise_certificates(product, official["declarations"]) != official["certifiedImportAllOriginalTypes"]:
            raise ValueError("live Promise import all certificates differ from inventory")
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


def promise_certificates(product, declarations):
    names = [row["name"] for row in declarations if row["module"] == PROMISE_OWNER and
             row["name"] in PROMISE_ELIMINATORS and row["matchingNameAndModule"]]
    if not names:
        return []
    result = subprocess.run(["lake", "env", "lean", "--run", HERE / "PromiseAccess.lean", product / "lib",
                             *(name.rsplit(".", 1)[1] for name in names)], cwd=ROOT,
                            stdout=subprocess.PIPE, text=True, check=True)
    certificates = [json.loads(line) for line in result.stdout.splitlines()]
    if certificates != [[PROMISE_OWNER, name, *PROMISE_TOKENS] for name in names]:
        raise ValueError("incomplete or unexpected Promise import all certificates")
    return certificates


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
    for owner in ("Init.Grind.Order", "Init.Grind.Ordered.Linarith", "Init.Grind.Ring.CommSolver",
                  "Init.Data.Sum.Lemmas", "Init.Data.Vector.Count", "Init.Data.Fin.Lemmas"):
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
        subprocess.run(["lake", "build", "+OmegaChecks.InitInventory", "+OmegaChecks.InitInventory.LinearEnvelopeOrder",
                        "+OmegaChecks.InitPort.Translation",
                        "+OmegaChecks.InitPort.StrictReplay", "+OmegaChecks.InitPort.PublicTypeClient", "+OmegaChecks.InitPort.SemiringImage",
                        "+OmegaChecks.InitPort.Alternatives.InternalOrder"], cwd=ROOT, check=True)
        subprocess.run(["lake", "env", "lean", "--run", HERE.parent / "InitInventory.lean", product / "lib", inventory],
                       cwd=ROOT, check=True)
        official = json.loads(inventory.read_text())
        with (product / "inventory.jsonl").open() as f:
            attempts = {}
            owners = defaultdict(list)
            for owner, name, _, why, dep in map(json.loads, f):
                attempts[owner, name] = (why, dep)
                owners[name].append(owner)
        promise_checks = promise_certificates(product, official["declarations"])
        official["certifiedImportAllOriginalTypes"] = promise_checks
        official["summary"]["importAllOriginalTypesChecked"] = len(promise_checks)
        promise_sites = {(owner, name) for owner, name, _, _ in promise_checks}
        order_checks = order_certificates(product)
        official["certifiedOrderTypeDependencies"] = order_checks
        orders = order_dependencies(order_checks)
        choice_checks = choice_type_certificates(product)
        official["certifiedChoiceTypeDependencies"] = choice_checks
        choice_operands = choice_type_dependencies(choice_checks)
        embedding_checks = envelope_type_certificates(product)
        official["certifiedEnvelopeTypeDependencies"] = embedding_checks
        embeddings = envelope_type_dependencies(embedding_checks)
        order_formations = envelope_formation_certificates(product)
        official["certifiedEnvelopeOrderFormations"] = order_formations
        comparison_formations = envelope_order_formations(order_formations)
        image_checks = envelope_formation_certificates(product, "SemiringEquationsCheck.lean")
        official["certifiedSemiringEquations"] = image_checks
        image_sites = semiring_image_sites(image_checks)
        specified_checks = envelope_formation_certificates(product, "SpecifiedChoiceCheck.lean")
        official["certifiedSpecifiedChoice"] = specified_checks
        specified = specified_choice_sites(specified_checks, official["declarations"])
        ring_checks = envelope_formation_certificates(product, "RingInstanceFormation.lean")
        official["certifiedRingInstanceFormations"] = ring_checks
        ring_formations = ring_instance_sites(ring_checks)
        order_coherence = envelope_type_certificates(product, order=True)
        official["certifiedEnvelopeOrderCoherence"] = order_coherence
        comparisons = envelope_order_dependencies(order_coherence)
        bound_checks = fin_bounds.certificates(product)
        official["certifiedFinBoundTypes"] = bound_checks
        official["summary"]["finBoundProofReplacementsChecked"] = len(bound_checks)
        equivalent = fin_bounds.sites(bound_checks)
        pointwise_checks = order_consumers.certificates(product)
        official["certifiedPointwiseOrderTypes"] = pointwise_checks
        official["summary"]["pointwiseOrderTypesChecked"] = len(pointwise_checks)
        pointwise_sites = order_consumers.sites(pointwise_checks)
        finite_checks = finite_consumers.certificates(product, official["declarations"])
        official["certifiedFiniteConsumerTypes"] = finite_checks
        official["summary"]["finiteConsumerTypesChecked"] = len(finite_checks)
        finite_sites = finite_consumers.sites(finite_checks)
        projection_checks = finite_consumers.certificates(product, official["declarations"], "projection")
        official["certifiedProjectionTypes"] = projection_checks
        official["summary"]["publicProjectionTypesChecked"] = len(projection_checks)
        projections = finite_consumers.sites(projection_checks)
        scope_checks = scoped_consumers.certificates(product, official["declarations"])
        official["certifiedModuleBodyTypes"] = scope_checks
        official["summary"]["moduleBodyTypesChecked"] = len(scope_checks)
        scopes = scoped_consumers.scopes(scope_checks)
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
            if site in scopes:
                row["moduleBodyStrictImport"] = scopes[site]
            if site in projections:
                row["publicProjectionTypeChecked"] = True
            if site in finite_sites:
                row["finiteConsumerTypeChecked"] = True
            if site in pointwise_sites:
                row["pointwiseOrderTypeChecked"] = True
            if site in equivalent:
                row["finBoundProofReplacementChecked"] = True
            if site in choice_operands:
                row["originalTypeChoiceDependency"] = choice_operands[site]
            if site in comparison_formations:
                row["quotientOrderFormation"] = comparison_formations[site]
            if site in image_sites:
                row["semiringImageEquation"] = image_sites[site]
            if site in specified:
                row["specifiedChoiceOperand"], row["specifiedChoiceObservation"] = specified[site]
            if site in ring_formations:
                row["quotientRingFormation"] = RING_INSTANCE
            if site in comparisons:
                row["originalTypeEnvelopeOrderInstance"] = comparisons[site]
            if site in embeddings:
                row["originalTypeEnvelopeInstance"] = ENVELOPE_INSTANCE
            if site in orders:
                row["originalTypeOrderDependencies"] = orders[site]
            if site in promise_sites:
                row["importAllOriginalTypeChecked"] = True
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
        official["summary"]["coverage"] = coverage_totals(official, unresolved)
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
                             "specializedEndpointType", "strictConstructorIff", "formationArgument", "transportPathType", "pinnedLiftCoherenceRefuter",
                             "strictLogicalConsequence", "strictLogicalConsequenceWitness", "strictEquivalenceWitness",
                             "representativeRefuter", "refinedQuotientConsequence", "originalTypeGap",
                             "importAllOriginalTypeChecked", "originalTypeOrderDependencies", "originalTypeChoiceDependency", "finBoundProofReplacementChecked",
                             "pointwiseOrderTypeChecked", "finiteConsumerTypeChecked", "publicProjectionTypeChecked", "moduleBodyStrictImport", "originalTypeEnvelopeInstance", "originalTypeEnvelopeOrderInstance", "quotientOrderFormation", "quotientRingFormation",
                             "specifiedChoiceOperand", "specifiedChoiceObservation", "semiringImageEquation"])
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
                                 row.get("formationArgument"), row.get("transportPathType"), row.get("pinnedLiftCoherenceRefuter"),
                                 row.get("strictLogicalConsequence"), row.get("strictLogicalConsequenceWitness"),
                                 row.get("strictEquivalenceWitness"), row.get("representativeRefuter"),
                                 row.get("refinedQuotientConsequence"), row.get("originalTypeGap"),
                                 "true" if row.get("importAllOriginalTypeChecked") else "",
                                 json.dumps(row["originalTypeOrderDependencies"], sort_keys=True) if row.get("originalTypeOrderDependencies") else "",
                                 row.get("originalTypeChoiceDependency"),
                                 "true" if row.get("finBoundProofReplacementChecked") else "",
                                 "true" if row.get("pointwiseOrderTypeChecked") else "",
                                 "true" if row.get("finiteConsumerTypeChecked") else "",
                                 "true" if row.get("publicProjectionTypeChecked") else "", row.get("moduleBodyStrictImport"), row.get("originalTypeEnvelopeInstance"),
                                 row.get("originalTypeEnvelopeOrderInstance"), row.get("quotientOrderFormation"), row.get("quotientRingFormation"),
                                 row.get("specifiedChoiceOperand"), row.get("specifiedChoiceObservation"), row.get("semiringImageEquation")])
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
    print(json.dumps(official["summary"]["coverage"]))
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
