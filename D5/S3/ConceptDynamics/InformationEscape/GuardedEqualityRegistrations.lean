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

register_information_template guardedEqRealization

section PositiveFirst
open D5.S3.ConceptDynamics.ExperimentDesign.AdaptiveEarlyStopping
open D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification

def modelXYCode : Fin 3 :=
  (⟨Nat.zero, (let h : Nat.lt 0 3 := (by change 0 < 3; omega); h)⟩ :
    Fin (Nat.succ (Nat.succ (Nat.succ Nat.zero))))

def positiveFirstReadout (model : Fin 3) : Bool :=
  @decide (model = modelXYCode) (instDecidableEqFin 3 model modelXYCode)
def positiveFirstArena := guardedEqArena (Arena.ofFintype (Fin 3)) (Fin 3)
def positiveFirstRealization := @guardedEqRealization (Fin 3) (Fin 3) (instDecidableEqFin 3)
  (fun model => positiveFirstReadout model) (fun model => model) (fun _ => modelXYCode)
theorem positiveFirst_bridge : LegacyPrimitiveRealization positiveFirstArena
    (∀ model : Fin 3, E_X model = true → model = M_XY) positiveFirstRealization := by
  exact ⟨Iff.rfl⟩
theorem positiveFirst_lawSensitive : positiveFirstArena.Law positiveFirstRealization ∧
    ¬ positiveFirstArena.Law (guardedEqRealization E_X (fun _ => M_0) (fun _ => M_XY)) := by
  exact ⟨positiveFirst_bridge.equivalence.mp positive_first_experiment_identifies_model,
    fun h => (by decide : M_0 ≠ M_XY) (h M_XY rfl)⟩
theorem positiveFirst_slotSensitive : FiniteSlotSensitivity positiveFirstArena :=
  guardedEq_sensitivity _ M_XY M_XY M_0 (by decide)
register_information_theorem positive_first_experiment_identifies_model in positiveFirstArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrationTemplates.guardedEqRealization
    (Fin 3) (Fin 3) (instDecidableEqFin 3)
    (fun model => positiveFirstReadout model) (fun model => model) (fun _ => modelXYCode))
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

def sourceZero : Fin 6 :=
  (⟨Nat.zero, (let h : Nat.lt 0 6 := (by change 0 < 6; omega); h)⟩ :
    Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))
def sourceOne : Fin 6 :=
  (⟨(Nat.succ Nat.zero), (let h : Nat.lt 1 6 := (by change 1 < 6; omega); h)⟩ :
    Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))
def dimension39Code : Fin 2 :=
  (⟨Nat.zero, (let h : Nat.lt 0 2 := (by change 0 < 2; omega); h)⟩ :
    Fin (Nat.succ (Nat.succ Nat.zero)))
def dimension40Code : Fin 2 :=
  (⟨(Nat.succ Nat.zero), (let h : Nat.lt 1 2 := (by change 1 < 2; omega); h)⟩ :
    Fin (Nat.succ (Nat.succ Nat.zero)))

def outerGuardReadout (i : Fin 6) : Bool :=
  Bool.rec (@decide (i = sourceOne) (instDecidableEqFin 6 i sourceOne)) true
    (@decide (i = sourceZero) (instDecidableEqFin 6 i sourceZero))
def outerDimensionReadout (i : Fin 6) : Fin 2 :=
  Bool.rec dimension39Code dimension40Code (outerGuardReadout i)
def outerDimensionCodeArena := guardedEqArena (Arena.ofFintype (Fin 6)) (Fin 2)
def outerDimensionRealization := @guardedEqRealization (Fin 6) (Fin 2) (instDecidableEqFin 2)
  (fun i => outerGuardReadout i) (fun i => outerDimensionReadout i) (fun _ => dimension40Code)
theorem outerDimension_bridge : LegacyPrimitiveRealization outerDimensionCodeArena
    (∀ g : PhysicalSourceGroup, g.isOuter = true → g.dimension = 40) outerDimensionRealization := by
  constructor
  change (∀ g : PhysicalSourceGroup, g.isOuter = true → g.dimension = 40) ↔
    ∀ i : Fin 6, outerGuardReadout i = true → outerDimensionReadout i = dimension40Code
  let encode : PhysicalSourceGroup → Fin 6
    | .outerH2 => 0 | .outerH25 => 1 | .oldInnerH2 => 2
    | .oldInnerH25 => 3 | .newInnerH2 => 4 | .newInnerH25 => 5
  let decode (i : Fin 6) : PhysicalSourceGroup :=
    if i = 0 then .outerH2 else if i = 1 then .outerH25 else if i = 2 then .oldInnerH2
    else if i = 3 then .oldInnerH25 else if i = 4 then .newInnerH2 else .newInnerH25
  have decodeEncode (g) : decode (encode g) = g := by cases g <;> decide
  have encodeDecode (i) : encode (decode i) = i := by fin_cases i <;> decide
  let coordinates : PhysicalSourceGroup ≃ Fin 6 := ⟨encode, decode, decodeEncode, encodeDecode⟩
  let encodeDimension (n : Nat) : Fin 2 := if n = 40 then 1 else 0
  let decodeDimension (i : Fin 2) : Nat := if i = 1 then 40 else 39
  have guardDecoded (i) : outerGuardReadout i = (coordinates.symm i).isOuter := by
    change outerGuardReadout i = (decode i).isOuter
    fin_cases i <;> decide
  have dimensionEncoded (i) :
      encodeDimension (coordinates.symm i).dimension = outerDimensionReadout i := by
    change encodeDimension (decode i).dimension = outerDimensionReadout i
    fin_cases i <;> decide
  have dimensionDecoded (i) :
      decodeDimension (encodeDimension (coordinates.symm i).dimension) =
        (coordinates.symm i).dimension := by
    change decodeDimension (encodeDimension (decode i).dimension) = (decode i).dimension
    fin_cases i <;> decide
  have fortyEncoded : encodeDimension 40 = dimension40Code := rfl
  have fortyDecoded : decodeDimension (encodeDimension 40) = 40 := rfl
  have outputIff (i) : outerDimensionReadout i = dimension40Code ↔
      (coordinates.symm i).dimension = 40 := by
    rw [← dimensionEncoded i, ← fortyEncoded]
    exact ⟨fun h => (dimensionDecoded i).symm.trans
      ((congrArg decodeDimension h).trans fortyDecoded), fun h => congrArg encodeDimension h⟩
  have pointwise (i) :
      (outerGuardReadout i = true → outerDimensionReadout i = dimension40Code) ↔
      ((coordinates.symm i).isOuter = true → (coordinates.symm i).dimension = 40) := by
    rw [guardDecoded, outputIff]
  constructor
  · intro h i
    exact (pointwise i).mpr (h (coordinates.symm i))
  · intro h g
    have atCode := (pointwise (coordinates g)).mp (h (coordinates g))
    simpa only [coordinates.symm_apply_apply] using atCode

theorem outerDimension_lawSensitive : outerDimensionCodeArena.Law outerDimensionRealization ∧
    ¬ outerDimensionCodeArena.Law
      (guardedEqRealization (fun i => outerGuardReadout i)
        (fun _ => dimension39Code) (fun _ => dimension40Code)) := by
  exact ⟨outerDimension_bridge.equivalence.mp dimension_eq_40_of_outer,
    fun h => (by decide : dimension39Code ≠ dimension40Code) (h (0 : Fin 6) rfl)⟩
theorem outerDimension_slotSensitive : FiniteSlotSensitivity outerDimensionCodeArena :=
  guardedEq_sensitivity _ (0 : Fin 6) dimension39Code dimension40Code (by decide)
register_information_theorem dimension_eq_40_of_outer in outerDimensionCodeArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrationTemplates.guardedEqRealization
    (Fin 6) (Fin 2) (instDecidableEqFin 2)
    (fun i => outerGuardReadout i) (fun i => outerDimensionReadout i) (fun _ => dimension40Code))
  primitives outerDimensionRealization.toPrimitiveBundle realization outerDimension_bridge
  variation outerDimension_lawSensitive sensitivity outerDimension_slotSensitive
example : dimension_eq_40_of_outer.__information_unit.Statement =
    (∀ (g : PhysicalSourceGroup) (_h : g.isOuter = true), g.dimension = 40) := rfl
#print axioms outerDimension_bridge
#print axioms outerDimension_lawSensitive
#print axioms outerDimension_slotSensitive
expect_information_occurrence dimension_eq_40_of_outer in outerDimensionCodeArena
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
