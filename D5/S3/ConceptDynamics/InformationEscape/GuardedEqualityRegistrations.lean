/- GID: D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.positiveFirst_lawSensitive; instance=D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.positiveFirstRealization
   digest: Two frozen conditional equations share one template while preserving their statements, guards and complete finite arenas. -/

import D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog
import D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification
import D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations

open GuardedEqualityRegistrationTemplates LeanInformationAudit

section PositiveFirst
open D5.S3.ConceptDynamics.ExperimentDesign.AdaptiveEarlyStopping
open D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification

def positiveFirstArena := guardedEqArena (Arena.ofFintype (Fin 3)) (Fin 3)
def positiveFirstRealization := guardedEqRealization E_X (fun model => model) (fun _ => M_XY)
theorem positiveFirst_bridge : LegacyPrimitiveRealization positiveFirstArena
    (∀ model : Fin 3, E_X model = true → model = M_XY) positiveFirstRealization :=
  guardedEqLegacy _ _ _ _
theorem positiveFirst_lawSensitive : positiveFirstArena.Law positiveFirstRealization ∧
    ¬ positiveFirstArena.Law (guardedEqRealization E_X (fun _ => M_0) (fun _ => M_XY)) := by
  exact ⟨positiveFirst_bridge.equivalence.mp positive_first_experiment_identifies_model,
    fun h => (by decide : M_0 ≠ M_XY) (h M_XY rfl)⟩
theorem positiveFirst_slotSensitive : FiniteSlotSensitivity positiveFirstArena :=
  guardedEq_sensitivity _ M_XY M_XY M_0 (by decide)
register_information_theorem positive_first_experiment_identifies_model in positiveFirstArena
  primitives positiveFirstRealization.toPrimitiveBundle realization positiveFirst_bridge
  variation positiveFirst_lawSensitive sensitivity positiveFirst_slotSensitive
example : positive_first_experiment_identifies_model.__information_unit.Statement =
    (∀ (model : Fin 3) (_hpositive : E_X model = true), model = M_XY) := rfl
#print axioms positiveFirst_bridge
#print axioms positiveFirst_lawSensitive
#print axioms positiveFirst_slotSensitive
expect_information_occurrence positive_first_experiment_identifies_model in positiveFirstArena
  from "D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations"
end PositiveFirst

section OuterDimension
open D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups

def outerDimensionArena := guardedEqArena (Arena.ofFintype PhysicalSourceGroup) ℕ
def outerDimensionRealization := guardedEqRealization PhysicalSourceGroup.isOuter
  PhysicalSourceGroup.dimension (fun _ => 40)
theorem outerDimension_bridge : LegacyPrimitiveRealization outerDimensionArena
    (∀ g : PhysicalSourceGroup, g.isOuter = true → g.dimension = 40) outerDimensionRealization :=
  guardedEqLegacy _ _ _ _
theorem outerDimension_lawSensitive : outerDimensionArena.Law outerDimensionRealization ∧
    ¬ outerDimensionArena.Law
      (guardedEqRealization PhysicalSourceGroup.isOuter (fun _ => 39) (fun _ => 40)) := by
  exact ⟨outerDimension_bridge.equivalence.mp dimension_eq_40_of_outer,
    fun h => (by decide : (39 : ℕ) ≠ 40) (h .outerH2 rfl)⟩
theorem outerDimension_slotSensitive : FiniteSlotSensitivity outerDimensionArena :=
  guardedEq_sensitivity _ PhysicalSourceGroup.outerH2 39 40 (by decide)
register_information_theorem dimension_eq_40_of_outer in outerDimensionArena
  primitives outerDimensionRealization.toPrimitiveBundle realization outerDimension_bridge
  variation outerDimension_lawSensitive sensitivity outerDimension_slotSensitive
example : dimension_eq_40_of_outer.__information_unit.Statement =
    (∀ (g : PhysicalSourceGroup) (_h : g.isOuter = true), g.dimension = 40) := rfl
#print axioms outerDimension_bridge
#print axioms outerDimension_lawSensitive
#print axioms outerDimension_slotSensitive
expect_information_occurrence dimension_eq_40_of_outer in outerDimensionArena
  from "D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations"
end OuterDimension

#seal_information_theory

open Lean in
run_meta do
  let env ← getEnv
  for entry in InformationRegistry.entries env do
    if entry.registrationModuleName == env.header.mainModule then
      let name := RegistrationGates.diagnosticName entry.unitName env.header.mainModule
      let info ← getConstInfo name
      let some (.lit (.strVal diagnostic)) := info.value?
        | throwError "registration diagnostic is not a literal"
      if diagnostic.isEmpty then
        logInfo m!"REGISTRATION_WITNESSES_CHECKED {entry.theoremName} \
          support=[readout[0],readout[1],readout[2]]"
      else
        logWarning diagnostic

end D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations
