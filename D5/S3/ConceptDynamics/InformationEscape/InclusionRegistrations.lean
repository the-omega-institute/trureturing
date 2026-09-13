/- GID: D5/S3/ConceptDynamics/InformationEscape/InclusionRegistrations
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/InclusionRegistrations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/InformationEscape/InclusionRegistrations.eight_lawSensitive; instance=D5/S3/ConceptDynamics/InformationEscape/InclusionRegistrations.eightRealization
   digest: Three frozen finset inclusions retain their exact statements through one finite-support ADMIT template. -/

import D5.S3.ConceptDynamics.InformationEscape.InclusionRegistrationTemplates
import D5.S0.Tower.GoldenPeriodic.EnumerationEight
import D5.S0.Tower.GoldenPeriodic.EnumerationNine
import D5.S0.Tower.TribonacciPeriodic.EnumerationSix
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.InclusionRegistrations

open InclusionRegistrationTemplates LeanInformationAudit

-- Finite support reflection must unfold the rational arithmetic in the code generators.
attribute [local semireducible] Rat.add Rat.sub Rat.mul Rat.inv

section Eight
open D5.S0.Tower.Champions.GoldenPeriodicEnumeration
open D5.S0.Tower.GoldenPeriodic.EnumerationEight

def eightArena := inclusionArena (Arena.ofFintype ↥(goldenInheritedPointCodesEight ∪ goldenPeriodicPointCodesSeven))
def eightRealization := inclusionRealization
  (fun x : ↥(goldenInheritedPointCodesEight ∪ goldenPeriodicPointCodesSeven) => x.val ∈ goldenInheritedPointCodesEight)
  (fun x => x.val ∈ goldenPeriodicPointCodesSeven)
def eightFirst : eightArena.State := ⟨⟨.large, (0, 0)⟩, by decide +kernel⟩
def eightSecond : eightArena.State := ⟨⟨.large, (1, 0)⟩, by decide +kernel⟩
example : eightArena.toArena.Nondegenerate := by
  letI := eightArena.toArena.stateFintype
  letI := eightArena.toArena.stateDecidableEq
  exact Fintype.one_lt_card_iff.mpr ⟨eightFirst, eightSecond, by decide⟩
theorem eight_bridge : LegacyPrimitiveRealization eightArena
    (goldenInheritedPointCodesEight ⊆ goldenPeriodicPointCodesSeven) eightRealization :=
  inclusionLegacy _ _
theorem eight_lawSensitive : eightArena.Law eightRealization ∧
    ¬ eightArena.Law (inclusionRealization (fun _ => True) (fun _ => False)) :=
  ⟨eight_bridge.equivalence.mp golden_inherited_point_codes_eight_subset_seven,
    fun h => Bool.noConfusion (h eightFirst rfl)⟩
theorem eight_slotSensitive : FiniteSlotSensitivity eightArena :=
  inclusion_sensitivity _ eightFirst
register_information_theorem golden_inherited_point_codes_eight_subset_seven in eightArena
  primitives eightRealization.toPrimitiveBundle realization eight_bridge
  variation eight_lawSensitive sensitivity eight_slotSensitive
example : golden_inherited_point_codes_eight_subset_seven.__information_unit.Statement =
    (goldenInheritedPointCodesEight ⊆ goldenPeriodicPointCodesSeven) := rfl
#print axioms eight_bridge
#print axioms eight_lawSensitive
#print axioms eight_slotSensitive
expect_information_occurrence golden_inherited_point_codes_eight_subset_seven in eightArena
  from "D5.S3.ConceptDynamics.InformationEscape.InclusionRegistrations"
end Eight

section Nine
open D5.S0.Tower.Champions.GoldenPeriodicEnumeration
open D5.S0.Tower.GoldenPeriodic.EnumerationEight
open D5.S0.Tower.GoldenPeriodic.EnumerationNine

def nineArena := inclusionArena (Arena.ofFintype ↥(goldenInheritedPointCodesNine ∪ goldenPeriodicPointCodesEight))
def nineRealization := inclusionRealization
  (fun x : ↥(goldenInheritedPointCodesNine ∪ goldenPeriodicPointCodesEight) => x.val ∈ goldenInheritedPointCodesNine)
  (fun x => x.val ∈ goldenPeriodicPointCodesEight)
def nineFirst : nineArena.State := ⟨⟨.large, (0, 0)⟩, by decide +kernel⟩
def nineSecond : nineArena.State := ⟨⟨.large, (1, 0)⟩, by decide +kernel⟩
example : nineArena.toArena.Nondegenerate := by
  letI := nineArena.toArena.stateFintype
  letI := nineArena.toArena.stateDecidableEq
  exact Fintype.one_lt_card_iff.mpr ⟨nineFirst, nineSecond, by decide⟩
theorem nine_bridge : LegacyPrimitiveRealization nineArena
    (goldenInheritedPointCodesNine ⊆ goldenPeriodicPointCodesEight) nineRealization :=
  inclusionLegacy _ _
theorem nine_lawSensitive : nineArena.Law nineRealization ∧
    ¬ nineArena.Law (inclusionRealization (fun _ => True) (fun _ => False)) :=
  ⟨nine_bridge.equivalence.mp golden_inherited_point_codes_nine_subset_eight,
    fun h => Bool.noConfusion (h nineFirst rfl)⟩
theorem nine_slotSensitive : FiniteSlotSensitivity nineArena :=
  inclusion_sensitivity _ nineFirst
register_information_theorem golden_inherited_point_codes_nine_subset_eight in nineArena
  primitives nineRealization.toPrimitiveBundle realization nine_bridge
  variation nine_lawSensitive sensitivity nine_slotSensitive
example : golden_inherited_point_codes_nine_subset_eight.__information_unit.Statement =
    (goldenInheritedPointCodesNine ⊆ goldenPeriodicPointCodesEight) := rfl
#print axioms nine_bridge
#print axioms nine_lawSensitive
#print axioms nine_slotSensitive
expect_information_occurrence golden_inherited_point_codes_nine_subset_eight in nineArena
  from "D5.S3.ConceptDynamics.InformationEscape.InclusionRegistrations"
end Nine

section Six
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.TribonacciPeriodic.EnumerationSix

def sixArena := inclusionArena (Arena.ofFintype ↥(tribonacciInheritedPointCodesSix ∪ tribonacciPeriodicPointCodesFive))
def sixRealization := inclusionRealization
  (fun x : ↥(tribonacciInheritedPointCodesSix ∪ tribonacciPeriodicPointCodesFive) => x.val ∈ tribonacciInheritedPointCodesSix)
  (fun x => x.val ∈ tribonacciPeriodicPointCodesFive)
def sixFirst : sixArena.State := ⟨⟨.large, ⟨0, 0, 0⟩⟩, by decide +kernel⟩
def sixSecond : sixArena.State := ⟨tribonacciChampionPeriodicOrbit.start, by decide +kernel⟩
example : sixArena.toArena.Nondegenerate := by
  letI := sixArena.toArena.stateFintype
  letI := sixArena.toArena.stateDecidableEq
  exact Fintype.one_lt_card_iff.mpr ⟨sixFirst, sixSecond, by decide⟩
theorem six_bridge : LegacyPrimitiveRealization sixArena
    (tribonacciInheritedPointCodesSix ⊆ tribonacciPeriodicPointCodesFive) sixRealization :=
  inclusionLegacy _ _
theorem six_lawSensitive : sixArena.Law sixRealization ∧
    ¬ sixArena.Law (inclusionRealization (fun _ => True) (fun _ => False)) :=
  ⟨six_bridge.equivalence.mp tribonacci_inherited_point_codes_six_subset_five,
    fun h => Bool.noConfusion (h sixFirst rfl)⟩
theorem six_slotSensitive : FiniteSlotSensitivity sixArena :=
  inclusion_sensitivity _ sixFirst
register_information_theorem tribonacci_inherited_point_codes_six_subset_five in sixArena
  primitives sixRealization.toPrimitiveBundle realization six_bridge
  variation six_lawSensitive sensitivity six_slotSensitive
example : tribonacci_inherited_point_codes_six_subset_five.__information_unit.Statement =
    (tribonacciInheritedPointCodesSix ⊆ tribonacciPeriodicPointCodesFive) := rfl
#print axioms six_bridge
#print axioms six_lawSensitive
#print axioms six_slotSensitive
expect_information_occurrence tribonacci_inherited_point_codes_six_subset_five in sixArena
  from "D5.S3.ConceptDynamics.InformationEscape.InclusionRegistrations"
end Six

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

end D5.S3.ConceptDynamics.InformationEscape.InclusionRegistrations
