import D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion
import D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative
import D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness
import LeanInformationAudit.SealCommand
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
namespace LeanInformationAudit.Tests.Seal.M3
open D5.S3.ConceptDynamics D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscapeArenas
local macro "expect_member " t:ident " in " a:ident : command =>
  `(command| expect_information_occurrence $t in $a from "LeanInformationAudit.Tests.Seal.M3")
section Intervention
open Interventions.InterventionCounterfactualSeparation Interventions.CounterfactualKernelStrictlyFiner
open Interventions.CounterfactualIdentifiabilityCriterion Sufficiency.SufficiencyIsTargetRelative
open Sufficiency.UniversalSufficiencyFactorization ConceptJoinUniversal
open FourthFifthArenas
attribute [local instance] modelFintype modelDecidableEq
def interventionRealization := InformationEscapeRealizations.FourthFifthRealizations.interventionRealization
theorem intervention_bridge : LegacyPrimitiveRealization interventionArena
    (∃ M N : DeterministicBoolSCM, Int M = Int N ∧ CF M ≠ CF N) interventionRealization :=
  InformationEscapeRealizations.FourthFifthRealizations.intervention_strictly_weaker_than_counterfactual_realization
register_information_theorem intervention_strictly_weaker_than_counterfactual in interventionArena
  primitives interventionRealization.toPrimitiveBundle realization intervention_bridge
expect_member intervention_strictly_weaker_than_counterfactual in interventionArena
theorem finer_bridge : LegacyPrimitiveRealization interventionArena
    ((∀ M N : DeterministicBoolSCM, CF M = CF N → Int M = Int N) ∧
      ∃ M N : DeterministicBoolSCM, Int M = Int N ∧ CF M ≠ CF N) interventionRealization := by
  refine ⟨Iff.trans ?_ intervention_bridge.equivalence⟩
  exact ⟨And.right, fun h => ⟨counterfactual_eq_implies_interventional_eq, h⟩⟩
register_information_theorem counterfactual_kernel_strictly_finer in interventionArena
  primitives interventionRealization.toPrimitiveBundle realization finer_bridge
expect_member counterfactual_kernel_strictly_finer in interventionArena
theorem fiber_bridge : LegacyPrimitiveRealization interventionArena
    (∃ μ M N, M ∈ couplingFiber allSingleWorldMarginals μ ∧
      N ∈ couplingFiber allSingleWorldMarginals μ ∧ CF M ≠ CF N) interventionRealization := by
  refine ⟨Iff.trans ?_ intervention_bridge.equivalence⟩
  constructor
  · rintro ⟨μ, M, N, hM, hN, hCF⟩
    exact ⟨M, N, hM.trans hN.symm, hCF⟩
  · rintro ⟨M, N, hInt, hCF⟩
    exact ⟨allSingleWorldMarginals M, M, N, rfl, hInt.symm, hCF⟩
register_information_theorem boolean_counterfactual_varies_on_coupling_fiber in interventionArena
  primitives interventionRealization.toPrimitiveBundle realization fiber_bridge
expect_member boolean_counterfactual_varies_on_coupling_fiber in interventionArena
theorem not_identifiable_bridge : LegacyPrimitiveRealization interventionArena
    (¬ ∃ f : (Bool → BooleanMarginal) → (Bool → Bool → Bool → Bool),
      CF = f ∘ allSingleWorldMarginals) interventionRealization := by
  classical
  refine ⟨Iff.trans ?_ intervention_bridge.equivalence⟩
  rw [counterfactual_identifiable_iff_constant_on_fiber]
  simp only [not_forall, exists_prop]
  rfl
register_information_theorem boolean_counterfactual_not_identifiable in interventionArena
  primitives interventionRealization.toPrimitiveBundle realization not_identifiable_bridge
expect_member boolean_counterfactual_not_identifiable in interventionArena
theorem target_bridge : LegacyPrimitiveRealization interventionArena
    (Refines (canonicalTargetReadout interventionMarginal) interventionMarginal ∧
      ¬ Refines (canonicalTargetReadout counterfactualJoint) interventionMarginal)
    interventionRealization := by
  classical
  let : Nonempty DeterministicBoolSCM := ⟨noEffectModel⟩
  refine ⟨Iff.trans ?_ intervention_bridge.equivalence⟩
  have self := universal_sufficiency_factorization interventionMarginal interventionMarginal
  have target := universal_sufficiency_factorization interventionMarginal counterfactualJoint
  rw [self.1, self.2, target.1, target.2]
  simp only [not_forall, exists_prop]
  exact ⟨And.right, fun h => ⟨fun _ _ hsame => hsame, h⟩⟩
register_information_theorem interventional_marginal_sufficient_but_counterfactual_joint_not
  in interventionArena primitives interventionRealization.toPrimitiveBundle realization target_bridge
expect_member interventional_marginal_sufficient_but_counterfactual_joint_not in interventionArena
end Intervention
section Observation
open D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
open D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness
open InformationEscapeArenas.ObservationIntervention
def observationRealization := InformationEscapeRealizations.ObservationIntervention.observationInterventionRealization
theorem observation_bridge : LegacyPrimitiveRealization observationInterventionArena
    (∃ M N : DeterministicBoolSCM, Obs M = Obs N ∧ Int M ≠ Int N) observationRealization :=
  InformationEscapeRealizations.ObservationIntervention.observation_strictly_weaker_than_intervention_realization
register_information_theorem observation_strictly_weaker_than_intervention in observationInterventionArena
  primitives observationRealization.toPrimitiveBundle realization observation_bridge
expect_member observation_strictly_weaker_than_intervention in observationInterventionArena
theorem profile_bridge : LegacyPrimitiveRealization observationInterventionArena
    (let profile : DeterministicBoolSCM → Option Bool → Bool → Bool × Bool :=
      fun M action => match action with | none => Obs M | some x => Int M x
    {p : DeterministicBoolSCM × DeterministicBoolSCM | Setoid.ker profile p.1 p.2} ⊂
      {p : DeterministicBoolSCM × DeterministicBoolSCM | Setoid.ker Obs p.1 p.2})
    observationRealization := by
  refine ⟨Iff.trans ?_ observation_bridge.equivalence⟩
  dsimp only
  rw [Set.ssubset_iff_exists]
  constructor
  · rintro ⟨_, ⟨M, N⟩, hObs, hProfile⟩
    refine ⟨M, N, hObs, fun hInt => hProfile ?_⟩
    funext action; cases action with
    | none => exact hObs
    | some x => exact congrFun hInt x
  · rintro ⟨M, N, hObs, hInt⟩
    refine ⟨fun _ h => congrFun h none, (M, N), hObs, fun h => hInt ?_⟩
    funext x; exact congrFun h (some x)
register_information_theorem intervention_kernel_strictly_finer_than_observation
  in observationInterventionArena primitives observationRealization.toPrimitiveBundle realization profile_bridge
expect_member intervention_kernel_strictly_finer_than_observation in observationInterventionArena
end Observation
open Lean Meta LeanInformationAudit
#guard_msgs (error) in
#seal_information_theory
run_cmd do
  let env ← getEnv
  let records := SealRecords.forRoot env env.header.mainModule
  unless records.map (·.theorems.size) == #[5, 2] && records.all (fun r =>
      r.theorems.all (fun t => t.uniqueCaptureCount == 0)) do throwError "M3 complete zero vectors"
  prepareInformationAnalysisStage env.header.mainModule
  let some staged := SealRecords.analysisForRoot? (← getEnv) env.header.mainModule
    | throwError "M3 missing stage"
  unless staged.systemCertificate == env.header.mainModule.str "__system_catalog_not_irredundant" do
    throwError "M3 system verdict"
  discard <| prepareInformationAnalysisExport env.header.mainModule [.analysis]
end LeanInformationAudit.Tests.Seal.M3
