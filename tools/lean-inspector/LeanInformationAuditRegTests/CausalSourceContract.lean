import Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
import Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner
import Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily
import Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion
import Reg.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative
import D5.S3.ConceptDynamics.DagSemantics.KnowledgeAlongDependency
import D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion

open Lean Meta LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open _root_.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner
open _root_.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion
open _root_.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative
open _root_.D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization
open _root_.D5.S3.ConceptDynamics.ConceptJoinUniversal
open _root_.D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open _root_.D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion
open _root_.D5.S3.ConceptDynamics.DagSemantics.KnowledgeAlongDependency
open Reg.Support.CausalSourceFamily

namespace LeanInformationAuditRegTests.CausalSourceContract

/-- Reject only the intended diagnostic; unrelated exceptions fail the test. -/
private def rejectsExactly (expected : String) (action : MetaM Unit) : MetaM Unit := do
  let failure ← try
    action
    pure none
  catch error => pure (some (← error.toMessageData.toString))
  unless failure == some expected do
    throwError "[FAIL] expected {expected}, received {failure}"
  logInfo m!"[PASS] {expected}"

run_meta do
  let pairs := #[
    (``intervention_strictly_weaker_than_counterfactual, ``separationArena),
    (``counterfactual_kernel_strictly_finer, ``strictnessArena)]
  let mut selection := #[]
  for (target, arena) in pairs do
    let env ← getEnv
    let events := (TemplateBinding.inventory env).filter fun event =>
      event.key.theoremName == target && event.key.objectArena == arena
    let #[event] := events | throwError "[FAIL] expected unique causal source occurrence: {target}"
    let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
      | throwError "[FAIL] causal source claim missing"
    let record ← TemplateBinding.assess event (some claim)
    let .declaredValidated cert := record.result
      | throwError "[FAIL] causal source binding: {(← TemplateBinding.recordJson record).compress}"
    let some binding := cert.sourceBinding | throwError "[FAIL] source binding missing"
    unless record.escape.bridgeKind == "source-equivalence" &&
        record.escape.fromObject.isSome &&
        record.escape.continuation.any (·.kind == "open") do
      throwError "[FAIL] incomplete four-slot source record"
    let sourceInfo ← getConstInfo target
    let sourceOwner := (RegistrationReifier.declaringModuleOf env target).getD .anonymous
    unless (binding.getObjValAs? String "source_name") == .ok target.toString &&
        (binding.getObjValAs? String "source_owner") == .ok sourceOwner.toString &&
        (binding.getObjValAs? Nat "telescope_size") == .ok 0 &&
        (binding.getObjValAs? Nat "level_count") == .ok 0 &&
        (binding.getObjValAs? (Array Nat) "coordinates") == .ok #[] do
      throwError "[FAIL] original source identity or complete telescope changed"
    let some selected := claim.escapeInput.sourceSelection
      | throwError "[FAIL] original source selection missing"
    let (scope, _) ← (SourceScope.resolve sourceInfo selected).run 524288
    unless scope.readouts.size == 2 && scope.telescope.isEmpty && scope.levels.isEmpty do
      throwError "[FAIL] original Boolean SCM source scope"
    -- This checks actual Int/CF observations against the raw compiler source paths.
    discard <| (SourceScope.validateFields scope (mkConst ``signature)
      (mkConst ``actual)).run 524288
    rejectsExactly "unclassified_form:source.actual_observation" do
      discard <| (SourceScope.validateFields scope (mkConst ``signature)
        (mkConst ``constantCF)).run 524288
    -- Full assessment has its own ordering: the descriptor differs from the
    -- valid record, while validateFields above isolates the observation check.
    let badReadout ← mkAppM ``Realization.readout #[mkConst ``constantCF]
    let badAnchor ← mkAppM ``Realization.anchor #[mkConst ``constantCF]
    let distorted ← mkAppM ``realize #[mkConst ``signature, badReadout, badAnchor]
    let changed ← TemplateBinding.assess event (some { claim with descriptor := some distorted })
    let .declaredUnresolved diagnostic := changed.result
      | throwError "[FAIL] altered descriptor was not rejected"
    unless (diagnostic.splitOn "rule=source.descriptor_actual ").length == 2 do
      throwError "[FAIL] altered descriptor diagnostic: {diagnostic}"
    logInfo "[PASS] full_assessment_source.descriptor_actual"
    if target == ``counterfactual_kernel_strictly_finer then
      -- Keep the existential pair verbatim but remove the universal inclusion.
      unless sourceInfo.type.isAppOfArity ``And 2 do
        throwError "[FAIL] strictness source is no longer the expected conjunction"
      rejectsExactly "unclassified_form:source.statement_reconstruction" do
        discard <| (SourceScope.reconstruct sourceInfo.type sourceInfo.type.getAppArgs[1]!).run 524288
    selection := selection.push (event.key.registrationModule, #[event.key])
    logInfo m!"[PASS] causal_source_declared_validated {target} evidence_ref={cert.evidenceRef}"
  let wires ← TemplateBinding.reportJson selection
  IO.FS.writeFile ((← Repository.root) / ".lake/build/causal-source-family-evidence.json")
    ((Json.arr wires).compress ++ "\n")

-- Canonical downstream objects are the same readouts on the same model.
example : actual.readout false () = allSingleWorldMarginals := rfl
example : actual.readout false () = interventionMarginal := rfl
example : actual.readout true () = counterfactualJoint := rfl

/-- The named pair is a target defect, not merely two differently named models. -/
theorem named_target_defect :
    (noEffectModel, flipEffectModel) ∈ defectRelation
      (actual.readout false ()) counterfactualJoint := named_separation

/-- The original identifiability theorem rules out the distorted reverse decoder. -/
theorem reverse_decoder_refuted :
    ¬ ∃ decode : IntTable → CFTable, CF = decode ∘ Int :=
  boolean_counterfactual_not_identifiable

/-- Canonical target-relative sufficiency consumes the upstream strictness theorem. -/
example :
    Refines (canonicalTargetReadout interventionMarginal) (actual.readout false ()) ∧
      ¬ Refines (canonicalTargetReadout counterfactualJoint) (actual.readout false ()) :=
  interventional_marginal_sufficient_but_counterfactual_joint_not

/-- The explicit named defect also refutes recovery via the general target criterion. -/
theorem named_defect_refutes_recovery :
    ¬ ∃ decode : IntTable → CFTable,
      counterfactualJoint = decode ∘ actual.readout false () := by
  let : Nonempty (signature.State ()) := ⟨noEffectModel⟩
  exact (target_recovery_criterion (actual.readout false ()) counterfactualJoint).2.2.2.mpr
    ⟨(noEffectModel, flipEffectModel), named_target_defect⟩

-- This edge has a global factorization proof. The separating pair alone cannot supply it.
def causalEdge (prerequisite dependent : Bool) : Prop :=
  prerequisite = false ∧ dependent = true

theorem causal_edge_refines : EdgeRefines causalEdge (fun role => actual.readout role ()) := by
  rintro _ _ ⟨rfl, rfl⟩
  exact ⟨collapse, funext intervention_eq_collapse_counterfactual⟩

theorem canonical_path_refines : Refines (actual.readout false ()) (actual.readout true ()) :=
  refines_of_reachable causal_edge_refines (Relation.ReflTransGen.single ⟨rfl, rfl⟩)

theorem canonical_path_shrinks_target_defects :
    defectRelation (actual.readout true ()) counterfactualJoint ⊆
      defectRelation (actual.readout false ()) counterfactualJoint :=
  defectRelation_antitone_of_reachable causal_edge_refines
    (Relation.ReflTransGen.single ⟨rfl, rfl⟩) counterfactualJoint

/-- With the very same target, CF removes the named defect that Int retains. -/
example : (noEffectModel, flipEffectModel) ∉
    defectRelation (actual.readout true ()) counterfactualJoint := by
  rintro ⟨same, different⟩
  exact different same

#print axioms named_target_defect
#print axioms reverse_decoder_refuted
#print axioms named_defect_refutes_recovery
#print axioms causal_edge_refines
#print axioms canonical_path_refines
#print axioms canonical_path_shrinks_target_defects
run_meta do
  for name in #[
      ``Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.SourceFamily.registration,
      ``Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration,
      ``named_target_defect, ``reverse_decoder_refuted, ``named_defect_refutes_recovery,
      ``causal_edge_refines, ``canonical_path_refines, ``canonical_path_shrinks_target_defects] do
    let axioms ← collectAxioms name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "[FAIL] unaccepted axiom closure: {name}: {axioms}"
  logInfo "[PASS] causal_records_and_downstream_checks_standard_axiom_closure"

end LeanInformationAuditRegTests.CausalSourceContract
