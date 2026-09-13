/- GID: D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitution_lawSensitive; instance=D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitutionRealization
   digest: Two frozen pointwise equations use one template, with exact statements and checked variation and support. -/

import D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog
import D5.S0.Tower.DBonacci.Substitution
import D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations

open PointwiseRegistrationTemplates LeanInformationAudit

section Substitution
open D5.S0.Tower.DBonacci.Substitution
open D5.S0.Tower.Tribonacci.Substitution (TribonacciGapLetter gapLetterSubstitution)

def substitutionArena := pointwiseEqArena (Arena.ofFintype (Fin 3)) (List TribonacciGapLetter)
def substitutionRealization := pointwiseEqRealization
  (fun label : Fin 3 => (gapLabelSubstitution 3 label.1).map tribonacciGapLetterOfLabel)
  (fun label : Fin 3 => gapLetterSubstitution (tribonacciGapLetterOfLabel label.1))
theorem substitution_bridge : LegacyPrimitiveRealization substitutionArena
    (∀ label : Fin 3, (gapLabelSubstitution 3 label.1).map tribonacciGapLetterOfLabel =
      gapLetterSubstitution (tribonacciGapLetterOfLabel label.1)) substitutionRealization :=
  pointwiseEqLegacy _ _ _
theorem substitution_lawSensitive : substitutionArena.Law substitutionRealization ∧
    ¬ substitutionArena.Law (pointwiseEqRealization (fun _ => []) (fun _ => [.small])) := by
  exact ⟨substitution_bridge.equivalence.mp gapLabelSubstitution_three_compatible,
    fun h => (by decide : ([] : List TribonacciGapLetter) ≠ [.small]) (h (0 : Fin 3))⟩
theorem substitution_slotSensitive : FiniteSlotSensitivity substitutionArena :=
  pointwiseEq_sensitivity _ (0 : Fin 3) [] [.small] (by decide)
register_information_theorem gapLabelSubstitution_three_compatible in substitutionArena
  primitives substitutionRealization.toPrimitiveBundle realization substitution_bridge
  variation substitution_lawSensitive sensitivity substitution_slotSensitive
example : gapLabelSubstitution_three_compatible.__information_unit.Statement =
    (∀ label : Fin 3, (gapLabelSubstitution 3 label.1).map tribonacciGapLetterOfLabel =
      gapLetterSubstitution (tribonacciGapLetterOfLabel label.1)) := rfl
#print axioms substitution_bridge
#print axioms substitution_lawSensitive
#print axioms substitution_slotSensitive
expect_information_occurrence gapLabelSubstitution_three_compatible in substitutionArena
  from "D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations"
end Substitution

section Recenter
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
open D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates

def recenterArena := pointwiseEqArena (Arena.ofFintype (Fin 3)) Point
def recenterRealization := pointwiseEqRealization
  (fun d : Fin 3 => recenter d (direction d)) (fun _ => (0, 0))
theorem recenter_bridge : LegacyPrimitiveRealization recenterArena
    (∀ d : Fin 3, recenter d (direction d) = (0, 0)) recenterRealization :=
  pointwiseEqLegacy _ _ _
theorem recenter_lawSensitive : recenterArena.Law recenterRealization ∧
    ¬ recenterArena.Law (pointwiseEqRealization (fun _ => (0, 0)) (fun _ => (1, 0))) := by
  exact ⟨recenter_bridge.equivalence.mp recenter_direction,
    fun h => (by decide : ((0, 0) : Point) ≠ (1, 0)) (h (0 : Fin 3))⟩
theorem recenter_slotSensitive : FiniteSlotSensitivity recenterArena :=
  pointwiseEq_sensitivity _ (0 : Fin 3) (0, 0) (1, 0) (by decide)
register_information_theorem recenter_direction in recenterArena
  primitives recenterRealization.toPrimitiveBundle realization recenter_bridge
  variation recenter_lawSensitive sensitivity recenter_slotSensitive
example : recenter_direction.__information_unit.Statement =
    (∀ d : Fin 3, recenter d (direction d) = (0, 0)) := rfl
#print axioms recenter_bridge
#print axioms recenter_lawSensitive
#print axioms recenter_slotSensitive
expect_information_occurrence recenter_direction in recenterArena
  from "D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations"
end Recenter

#seal_information_theory

open Lean in
run_meta do
  let env ← getEnv
  for entry in InformationRegistry.entries env do
    if entry.registrationModuleName == env.header.mainModule then
      let info ← getConstInfo (RegistrationGates.diagnosticName entry.unitName env.header.mainModule)
      let some (.lit (.strVal diagnostic)) := info.value?
        | throwError "registration diagnostic is not a literal"
      if diagnostic.isEmpty then
        logInfo m!"REGISTRATION_WITNESSES_CHECKED {entry.theoremName} support=[readout[0],readout[1]]"
      else
        logWarning diagnostic

end D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations
