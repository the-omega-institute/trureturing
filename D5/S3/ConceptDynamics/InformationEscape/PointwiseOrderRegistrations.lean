/- GID: D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.positive_lawSensitive; instance=D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.positiveRealization
   digest: Strict and weak substitution bounds retain their source statements in one shared catalog. -/

import D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscape.EscapeRecord
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog
import D5.S1.Words.Powers.GoldenDesubstitution
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations

open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord D5.S3.ConceptDynamics.CIRPT

register_information_template homogeneousPointwiseOrderRealization
open D5.S1.Words.Powers D5.S0.Tower.GoldenGapWord

def lengthZero : Fin 3 := (⟨Nat.zero, (let h : Nat.lt 0 3 := (by change 0 < 3; omega); h)⟩ : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))
def lengthOne : Fin 3 := (⟨Nat.succ (Nat.zero), (let h : Nat.lt 1 3 := (by change 1 < 3; omega); h)⟩ : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))
def lengthTwo : Fin 3 := (⟨Nat.succ (Nat.succ (Nat.zero)), (let h : Nat.lt 2 3 := (by change 2 < 3; omega); h)⟩ : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))

def objectArena : Arena := Arena.ofFintype Bool
def strictArena := homogeneousPointwiseOrderArena objectArena (Fin 3) true
def weakArena := homogeneousPointwiseOrderArena objectArena (Fin 3) false
theorem strict_slotSensitive : FiniteSlotSensitivity strictArena :=
  homogeneousPointwiseOrder_sensitivity _ true false (0 : Fin 3) 1 (by decide)
theorem weak_slotSensitive : FiniteSlotSensitivity weakArena :=
  homogeneousPointwiseOrder_sensitivity _ false false (0 : Fin 3) 1 (by decide)

def lengthReadout (b : Bool) : Fin 3 := Bool.rec lengthOne lengthTwo b

def positiveRealization := @homogeneousPointwiseOrderRealization Bool (Fin 3)
  (instDecidableEqFin 3) (fun _ => lengthZero) (fun b => lengthReadout b)
theorem positive_bridge : LegacyPrimitiveRealization strictArena
    (∀ b : Bool, 0 < (subst b).length) positiveRealization := by
  constructor
  change (∀ b : Bool, 0 < (subst b).length) ↔ ∀ b : Bool, (0 : Fin 3) < lengthReadout b
  have encoded (b : Bool) : (lengthReadout b).val = (subst b).length := by
    cases b <;> rfl
  constructor
  · intro h b
    change 0 < (lengthReadout b).val
    simpa only [encoded] using h b
  · intro h b
    have hb : 0 < (lengthReadout b).val := h b
    simpa only [encoded] using hb
theorem positive_lawSensitive : strictArena.Law positiveRealization ∧
    ¬ strictArena.Law (homogeneousPointwiseOrderRealization (fun _ : Bool => (0 : Fin 3)) (fun _ => 0)) :=
  ⟨positive_bridge.equivalence.mp substLength_pos, fun h => lt_irrefl (0 : Fin 3) (h false)⟩

private def positiveChain : LayerChain strictArena.toArena where
  length := 0
  kernel := fun _ => cutKernel (fun b : Bool => (lengthZero, lengthReadout b))
  refines := fun r => Fin.elim0 r

private theorem positive_empty : EscapeResidualEmpty positiveChain := by
  change positiveChain.unresolvedCount = 0
  decide +kernel

register_information_theorem substLength_pos in strictArena
  object_arena objectArena catalog substitutionBounds
  readout via (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseOrderRealization
    Bool (Fin 3) (instDecidableEqFin 3)
    (fun _ => lengthZero) (fun b => D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.lengthReadout b))
  primitives positiveRealization.toPrimitiveBundle realization positive_bridge
  variation positive_lawSensitive sensitivity strict_slotSensitive
  escape from (Bool) escape continues (positive_empty)
example : substLength_pos.«D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations/D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena/substitutionBounds».__information_unit.Statement =
    (∀ b : Bool, 0 < (subst b).length) := rfl
#print axioms positive_bridge
#print axioms positive_lawSensitive
expect_information_occurrence substLength_pos in objectArena
  from "D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations"

def upperRealization := @homogeneousPointwiseOrderRealization Bool (Fin 3)
  (instDecidableEqFin 3) (fun b => lengthReadout b) (fun _ => lengthTwo)
theorem upper_bridge : LegacyPrimitiveRealization weakArena
    (∀ b : Bool, (subst b).length ≤ 2) upperRealization := by
  constructor
  change (∀ b : Bool, (subst b).length ≤ 2) ↔ ∀ b : Bool, lengthReadout b ≤ (2 : Fin 3)
  have encoded (b : Bool) : (lengthReadout b).val = (subst b).length := by
    cases b <;> rfl
  constructor
  · intro h b
    change (lengthReadout b).val ≤ 2
    simpa only [encoded] using h b
  · intro h b
    have hb : (lengthReadout b).val ≤ 2 := h b
    simpa only [encoded] using hb
theorem upper_lawSensitive : weakArena.Law upperRealization ∧
    ¬ weakArena.Law (homogeneousPointwiseOrderRealization (fun _ : Bool => (1 : Fin 3)) (fun _ => 0)) :=
  ⟨upper_bridge.equivalence.mp substLength_le_two, fun h => (by decide : ¬ (1 : Fin 3) ≤ 0) (h false)⟩

private def upperChain : LayerChain weakArena.toArena where
  length := 0
  kernel := fun _ => cutKernel (fun b : Bool => (lengthReadout b, lengthTwo))
  refines := fun r => Fin.elim0 r

private theorem upper_empty : EscapeResidualEmpty upperChain := by
  change upperChain.unresolvedCount = 0
  decide +kernel

register_information_theorem substLength_le_two in weakArena
  object_arena objectArena catalog substitutionBounds
  readout via (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseOrderRealization
    Bool (Fin 3) (instDecidableEqFin 3)
    (fun b => D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.lengthReadout b) (fun _ => lengthTwo))
  primitives upperRealization.toPrimitiveBundle realization upper_bridge
  variation upper_lawSensitive sensitivity weak_slotSensitive
  escape from (Bool) escape continues (upper_empty)
example : substLength_le_two.«D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations/D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena/substitutionBounds».__information_unit.Statement =
    (∀ b : Bool, (subst b).length ≤ 2) := rfl
#print axioms upper_bridge
#print axioms upper_lawSensitive
expect_information_occurrence substLength_le_two in objectArena
  from "D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations"

#print axioms strict_slotSensitive
#print axioms weak_slotSensitive
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

end D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations

-- probe: byte change that keeps this module's forbidden imports unchanged
