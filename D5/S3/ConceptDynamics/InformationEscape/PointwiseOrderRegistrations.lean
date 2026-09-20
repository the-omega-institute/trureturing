/- GID: D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.positive_lawSensitive; instance=D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.positiveRealization
   digest: Strict and weak substitution bounds retain their source statements in one shared catalog. -/

import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscape.EscapeRecord
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog
import D5.S1.Words.Powers.GoldenDesubstitution


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations

open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord D5.S3.ConceptDynamics.CIRPT


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

theorem positive_empty : EscapeResidualEmpty positiveChain := by
  change positiveChain.unresolvedCount = 0
  decide +kernel



#print axioms positive_bridge
#print axioms positive_lawSensitive


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

theorem upper_empty : EscapeResidualEmpty upperChain := by
  change upperChain.unresolvedCount = 0
  decide +kernel



#print axioms upper_bridge
#print axioms upper_lawSensitive


#print axioms strict_slotSensitive
#print axioms weak_slotSensitive




end D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations
