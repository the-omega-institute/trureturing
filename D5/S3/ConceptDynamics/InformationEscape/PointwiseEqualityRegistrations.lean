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

register_information_template homogeneousPointwiseEqRealization

section Substitution
open D5.S0.Tower.DBonacci.Substitution
open D5.S0.Tower.Tribonacci.Substitution (TribonacciGapLetter gapLetterSubstitution)

def substitutionArena := homogeneousPointwiseEqArena (Arena.ofFintype (Fin 3)) (Fin 3)
def substitutionRealization := @homogeneousPointwiseEqRealization
  (Fin 3) (Fin 3) (instDecidableEqFin 3) (fun label => label) (fun label => label)
theorem substitution_bridge : LegacyPrimitiveRealization substitutionArena
    (∀ label : Fin 3, (gapLabelSubstitution 3 label.1).map tribonacciGapLetterOfLabel =
      gapLetterSubstitution (tribonacciGapLetterOfLabel label.1)) substitutionRealization := by
  constructor
  change (∀ label : Fin 3, (gapLabelSubstitution 3 label.1).map tribonacciGapLetterOfLabel =
    gapLetterSubstitution (tribonacciGapLetterOfLabel label.1)) ↔ ∀ label : Fin 3, label = label
  let encode (xs : List TribonacciGapLetter) : Fin 3 :=
    if xs = [.large] then 0 else if xs = [.large, .small] then 1 else 2
  let decode (i : Fin 3) : List TribonacciGapLetter :=
    if i = 0 then [.large] else if i = 1 then [.large, .small] else [.large, .combined]
  have lhsEncoded (label : Fin 3) :
      encode ((gapLabelSubstitution 3 label.1).map tribonacciGapLetterOfLabel) = label := by
    fin_cases label <;> decide
  have rhsEncoded (label : Fin 3) :
      encode (gapLetterSubstitution (tribonacciGapLetterOfLabel label.1)) = label := by
    fin_cases label <;> decide
  have lhsDecoded (label : Fin 3) :
      decode (encode ((gapLabelSubstitution 3 label.1).map tribonacciGapLetterOfLabel)) =
        (gapLabelSubstitution 3 label.1).map tribonacciGapLetterOfLabel := by
    fin_cases label <;> decide
  have rhsDecoded (label : Fin 3) :
      decode (encode (gapLetterSubstitution (tribonacciGapLetterOfLabel label.1))) =
        gapLetterSubstitution (tribonacciGapLetterOfLabel label.1) := by
    fin_cases label <;> decide
  have codeIff (label : Fin 3) :
      encode ((gapLabelSubstitution 3 label.1).map tribonacciGapLetterOfLabel) =
        encode (gapLetterSubstitution (tribonacciGapLetterOfLabel label.1)) ↔
      (gapLabelSubstitution 3 label.1).map tribonacciGapLetterOfLabel =
        gapLetterSubstitution (tribonacciGapLetterOfLabel label.1) :=
    ⟨fun h => (lhsDecoded label).symm.trans ((congrArg decode h).trans (rhsDecoded label)),
      fun h => congrArg encode h⟩
  exact ⟨fun h label => by simpa only [lhsEncoded, rhsEncoded] using (codeIff label).mpr (h label),
    fun h label => (codeIff label).mp (by simpa only [lhsEncoded, rhsEncoded] using h label)⟩
theorem substitution_lawSensitive : substitutionArena.Law substitutionRealization ∧
    ¬ substitutionArena.Law (homogeneousPointwiseEqRealization (fun _ => (0 : Fin 3)) (fun _ => 1)) := by
  exact ⟨substitution_bridge.equivalence.mp gapLabelSubstitution_three_compatible,
    fun h => (by decide : (0 : Fin 3) ≠ 1) (h (0 : Fin 3))⟩
theorem substitution_slotSensitive : FiniteSlotSensitivity substitutionArena :=
  homogeneousPointwiseEq_sensitivity _ (0 : Fin 3) (0 : Fin 3) 1 (by decide)
register_information_theorem gapLabelSubstitution_three_compatible in substitutionArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqRealization
    (Fin 3) (Fin 3) (instDecidableEqFin 3)
    (fun label => label) (fun label => label))
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

def recenterReadout (_ : Fin 3) : Fin 2 := (⟨Nat.zero, (let h : Nat.lt 0 2 := (by change 0 < 2; omega); h)⟩ : Fin (Nat.succ (Nat.succ (Nat.zero))))
def recenterArena := homogeneousPointwiseEqArena (Arena.ofFintype (Fin 3)) (Fin 2)
def recenterRealization := @homogeneousPointwiseEqRealization (Fin 3) (Fin 2)
  (instDecidableEqFin 2) (fun d => recenterReadout d) (fun d => recenterReadout d)
theorem recenter_bridge : LegacyPrimitiveRealization recenterArena
    (∀ d : Fin 3, recenter d (direction d) = (0, 0)) recenterRealization := by
  constructor
  change (∀ d : Fin 3, recenter d (direction d) = (0, 0)) ↔
    ∀ d : Fin 3, recenterReadout d = recenterReadout d
  let encode (p : Point) : Fin 2 := if p = (0, 0) then 0 else 1
  let decode (i : Fin 2) : Point := if i = 0 then (0, 0) else (1, 0)
  have lhsEncoded (d : Fin 3) : encode (recenter d (direction d)) = recenterReadout d := by
    fin_cases d <;> decide
  have rhsEncoded (d : Fin 3) : encode (0, 0) = recenterReadout d := rfl
  have lhsDecoded (d : Fin 3) :
      decode (encode (recenter d (direction d))) = recenter d (direction d) := by
    fin_cases d <;> decide
  have rhsDecoded : decode (encode (0, 0)) = (0, 0) := rfl
  have codeIff (d : Fin 3) : encode (recenter d (direction d)) = encode (0, 0) ↔
      recenter d (direction d) = (0, 0) :=
    ⟨fun h => (lhsDecoded d).symm.trans ((congrArg decode h).trans rhsDecoded),
      fun h => congrArg encode h⟩
  exact ⟨fun h d => by simpa only [lhsEncoded, rhsEncoded d] using (codeIff d).mpr (h d),
    fun h d => (codeIff d).mp (by simpa only [lhsEncoded, rhsEncoded d] using h d)⟩
theorem recenter_lawSensitive : recenterArena.Law recenterRealization ∧
    ¬ recenterArena.Law (homogeneousPointwiseEqRealization (fun _ => (0 : Fin 2)) (fun _ => 1)) := by
  exact ⟨recenter_bridge.equivalence.mp recenter_direction,
    fun h => (by decide : (0 : Fin 2) ≠ 1) (h (0 : Fin 3))⟩
theorem recenter_slotSensitive : FiniteSlotSensitivity recenterArena :=
  homogeneousPointwiseEq_sensitivity _ (0 : Fin 3) (0 : Fin 2) 1 (by decide)
register_information_theorem recenter_direction in recenterArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqRealization
    (Fin 3) (Fin 2) (instDecidableEqFin 2)
    (fun d => D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterReadout d) (fun d => D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterReadout d))
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
