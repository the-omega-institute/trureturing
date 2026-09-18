import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates

namespace LeanInformationAudit.Tests.DeclaredProofBindings
open Lean Meta Elab Command TemplateAudit TemplateBinding
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

-- Named proofs prevent Lean's auxiliary-theorem cache from replacing all three
-- inputs by the same closed proof before the judge sees them.
theorem termProof : Nat.lt Nat.zero 4 := Nat.zero_lt_succ 3
theorem omegaProof : Nat.lt Nat.zero 4 := by change 0 < 4; omega
theorem decideProof : Nat.lt Nat.zero 4 := by change 0 < 4; decide

def termBound : PrimitiveRealization (cutSignature Bool (Fin 4)) :=
  cutRealization (fun _ => ⟨Nat.zero,
    termProof⟩)
def omegaBound : PrimitiveRealization (cutSignature Bool (Fin 4)) :=
  cutRealization (fun _ => ⟨Nat.zero,
    omegaProof⟩)
def decideBound : PrimitiveRealization (cutSignature Bool (Fin 4)) :=
  cutRealization (fun _ => ⟨Nat.zero,
    decideProof⟩)

-- Reuse one kernel-checked declaration address in independent environments.
-- Owners, source inputs and names are identical; only the proof term varies.
elab "observe_proof_plan_identities" : command => do
  let initial ← get
  let probe := (← getCurrNamespace).str "proofVariant"
  let mut plans : Array TemplatePlanData := #[]
  let mut directIdentities : Array String := #[]
  let mut rawIdentities : Array String := #[]
  let mut exactInput := true
  for name in #[``termBound, ``omegaBound, ``decideBound] do
    set initial
    let .defnInfo definition ← getConstInfo name | throwError "[FAIL] proof_variant_setup"
    let .ok (rawIdentity, _) := rawStatementIdentity definition.levelParams definition.value
      | throwError "[FAIL] proof_variant_raw_setup"
    rawIdentities := rawIdentities.push rawIdentity
    let .ok (directIdentity, _) ← liftTermElabM <| TemplateAudit.rawIdentity definition.levelParams definition.value
      | throwError "[FAIL] proof_variant_identity_setup"
    directIdentities := directIdentities.push directIdentity
    liftCoreM <| addDecl (.defnDecl { definition with name := probe, all := [probe] })
    let .defnInfo actual ← getConstInfo probe | throwError "[FAIL] proof_variant_setup"
    exactInput := exactInput && actual.value.equal definition.value
    let result ← enroll probe
    match selectedPlan (← getEnv) probe with
    | .ok plan => plans := plans.push plan
    | .error error => logError m!"[FAIL] proof_variant_enrolled {name}: {error}; {repr result}"
  set initial
  let bodies := plans.map (·.bodyIdentity)
  let identities := plans.map (·.planIdentity)
  let noProofDependencies := plans.all fun plan => plan.dependencies.all fun dep =>
    !#[``termProof, ``omegaProof, ``decideProof, `Nat.zero_lt_succ,
      `of_decide_eq_true, `lcProof].contains dep.name
  logInfo m!"[MEASURE] proof raw identities={rawIdentities}; direct={directIdentities}; plan bodies={bodies}"
  for (label, ok) in #[
      ("proof_variants_exact_input", exactInput),
      ("proof_variants_direct_identity", directIdentities.size == 3 && directIdentities.all (· == directIdentities[0]!)),
      ("proof_variants_distinct_inputs", rawIdentities.size == 3 &&
        rawIdentities[0]! != rawIdentities[1]! && rawIdentities[1]! != rawIdentities[2]! &&
        rawIdentities[0]! != rawIdentities[2]!),
      ("proof_variants_body_identity", plans.size == 3 && bodies.all (· == bodies[0]!)),
      ("proof_variants_plan_identity", plans.size == 3 && identities.all (· == identities[0]!)),
      ("proof_dependencies_absent", plans.size == 3 && noProofDependencies)] do
    (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"

observe_proof_plan_identities

-- Constructor description fields enter the same compiler as template bodies.
def discardTrue (_h : True) : Bool := true
def keepBool (b : Bool) : Bool := b

elab "observe_constructor_proof_identity" : command => do
  let initial ← get
  let ast := (← getCurrNamespace).str "ProofAST"
  let ctor := ast.str "mk"
  let proofs := #[mkConst ``True.intro,
    Expr.letE `h (mkConst ``True) (mkConst ``True.intro) (.bvar 0) false]
  let mut plans : Array TemplatePlanData := #[]
  let mut rawTypes : Array String := #[]
  for proof in proofs do
    set initial
    let domain ← liftTermElabM do
      let value ← mkAppM ``discardTrue #[proof]
      let value ← mkAppM ``keepBool #[value]
      mkEq value (mkConst ``Bool.true)
    let ctorType := mkForall `h .default domain (mkConst ast)
    liftCoreM <| addDecl (.inductDecl [] 0
      [{ name := ast, type := mkSort (.succ .zero),
         ctors := [{ name := ctor, type := ctorType }] }] false)
    let info ← getConstInfo ctor
    let .ok (identity, _) := rawStatementIdentity [] info.type
      | throwError "[FAIL] constructor_proof_raw_setup"
    rawTypes := rawTypes.push identity
    let result ← enroll ``cutRealization #[ast]
    match selectedPlan (← getEnv) ``cutRealization with
    | .ok plan => plans := plans.push plan
    | .error error => logError m!"[FAIL] constructor_proof_enrolled {error}; {repr result}"
  set initial
  let work := plans.map (·.chargedWork)
  logInfo m!"[MEASURE] constructor proof raw types={rawTypes}; work={work}"
  for (label, ok) in #[
      ("constructor_proof_raw_inputs_distinct", rawTypes.size == 2 && rawTypes[0]! != rawTypes[1]!),
      ("constructor_proof_work_identity", plans.size == 2 && work[0]! == work[1]!),
      ("constructor_proof_plan_identity", plans.size == 2 &&
        plans[0]!.planIdentity == plans[1]!.planIdentity)] do
    (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"

observe_constructor_proof_identity

register_information_template cutRealization
register_information_template termBound

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool (Fin 4)
  Law r := ∀ x : Bool, (r.readout () x).val = Nat.zero

instance : DecidableEq arena.State := instDecidableEqBool

theorem suppliedLaw : arena.Law omegaBound := by intro x; rfl
theorem suppliedBridge : LegacyPrimitiveRealization arena (arena.Law omegaBound) omegaBound :=
  ⟨Iff.rfl⟩
register_information_theorem suppliedLaw in arena
  readout via (@cutRealization Bool (Fin 4) (instDecidableEqFin 4) (fun _ =>
    ⟨Nat.zero, (let h : Nat.lt Nat.zero 4 := (by change 0 < 4; decide); h)⟩))
  primitives omegaBound.toPrimitiveBundle realization suppliedBridge

def literalBound : PrimitiveRealization (cutSignature Bool (Fin 4)) where
  readout := fun _ _ => ⟨Nat.zero,
    (let h : Nat.lt Nat.zero 4 := (by change 0 < 4; decide); h)⟩
  anchor := Fin.elim0

theorem planLaw : arena.Law literalBound := by intro x; rfl
theorem planBridge : LegacyPrimitiveRealization arena (arena.Law literalBound) literalBound := ⟨Iff.rfl⟩
register_information_theorem planLaw in arena
  readout via (termBound)
  primitives literalBound.toPrimitiveBundle realization planBridge

elab "observe_proof_bindings" : command => do
  for (label, name) in #[("proof_supplied_binding_validated", ``suppliedLaw),
      ("proof_plan_binding_validated", ``planLaw)] do
    let record := (records (← getEnv)).find? (·.occurrence.key.theoremName == name)
    let ok := record.any fun row => row.result matches .declaredValidated _
    (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"
    if let some { result := .declaredUnresolved diagnostic, .. } := record then logInfo diagnostic

observe_proof_bindings

end LeanInformationAudit.Tests.DeclaredProofBindings
