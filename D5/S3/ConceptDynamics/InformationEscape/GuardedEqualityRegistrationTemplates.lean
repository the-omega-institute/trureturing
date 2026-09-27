/- GID: D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A varying Boolean guard and two typed equality readouts retain the full arena with independent slot sensitivity. -/

import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import D5.S3.ConceptDynamics.RegistrationWitnesses

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrationTemplates

open LeanInformationAudit

/-- The three slot labels are finite data; only Boolean eliminators dispatch them. -/
def guardSlot : Fin 3 :=
  (⟨Nat.zero, (let h : Nat.lt 0 3 := (by change 0 < 3; omega); h)⟩ :
    Fin (Nat.succ (Nat.succ (Nat.succ Nat.zero))))
def leftSlot : Fin 3 :=
  (⟨Nat.succ Nat.zero, (let h : Nat.lt 1 3 := (by change 1 < 3; omega); h)⟩ :
    Fin (Nat.succ (Nat.succ (Nat.succ Nat.zero))))
def isGuardSlot (i : Fin 3) : Bool :=
  @decide (i = guardSlot) (instDecidableEqFin 3 i guardSlot)
def isLeftSlot (i : Fin 3) : Bool :=
  @decide (i = leftSlot) (instDecidableEqFin 3 i leftSlot)

/-- One ADMIT guard and two CUT terms; no state is removed by the guard. -/
abbrev guardedEqSignature (X Y : Type) [dY : DecidableEq Y] : PrimitiveSignature X where
  Index := Fin 3
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun i => Bool.rec Y Bool (isGuardSlot i)
  outputDecidableEq := fun i => Bool.rec (motive := fun b => DecidableEq (Bool.rec Y Bool b))
    dY instDecidableEqBool (isGuardSlot i)
  axis := fun i => Bool.rec .cut .admit (isGuardSlot i)
  readoutAxisNotAnchor := by intro i; fin_cases i <;> simp [isGuardSlot, guardSlot]
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def guardedEqRealization {X Y : Type} [dY : DecidableEq Y]
    (guard : X → Bool) (f g : X → Y) : PrimitiveRealization (guardedEqSignature X Y) where
  readout := fun i x => Bool.rec (motive := fun b => Bool.rec Y Bool b)
    (Bool.rec (g x) (f x) (isLeftSlot i)) (guard x) (isGuardSlot i)
  anchor := Fin.elim0

def guardedEqArena (A : Arena) (Y : Type) [DecidableEq Y] : PrimitiveLawArena where
  toArena := A
  signature := guardedEqSignature A.State Y
  Law r := ∀ x, r.readout 0 x = true → r.readout 1 x = r.readout 2 x

theorem guardedEqLegacy (A : Arena) {Y : Type} [DecidableEq Y]
    (guard : A.State → Bool) (f g : A.State → Y) :
    LegacyPrimitiveRealization (guardedEqArena A Y) (∀ x, guard x = true → f x = g x)
      (guardedEqRealization guard f g) := ⟨Iff.rfl⟩

/-- The guard and each equality term can independently change the law. -/
theorem guardedEq_sensitivity (A : Arena) {Y : Type} [DecidableEq Y]
    (x : A.State) (a b : Y) (hne : a ≠ b) : FiniteSlotSensitivity (guardedEqArena A Y) := by
  constructor
  · intro i
    change Fin 3 at i
    fin_cases i
    · refine ⟨guardedEqRealization (fun _ => false) (fun _ => a) (fun _ => b),
        guardedEqRealization (fun _ => true) (fun _ => a) (fun _ => b), ?_, ?_, ?_⟩
      · intro j hj; change Fin 3 at j; fin_cases j
        · exact (hj rfl).elim
        · rfl
        · rfl
      · intro j; exact Fin.elim0 j
      · exact ⟨fun _ h => hne (h x rfl), fun _ _ h => Bool.noConfusion h⟩
    · refine ⟨guardedEqRealization (fun _ => true) (fun _ => a) (fun _ => a),
        guardedEqRealization (fun _ => true) (fun _ => b) (fun _ => a), ?_, ?_, ?_⟩
      · intro j hj; change Fin 3 at j; fin_cases j
        · rfl
        · exact (hj rfl).elim
        · rfl
      · intro j; exact Fin.elim0 j
      · exact ⟨fun _ h => hne (h x rfl).symm, fun _ _ _ => rfl⟩
    · refine ⟨guardedEqRealization (fun _ => true) (fun _ => a) (fun _ => a),
        guardedEqRealization (fun _ => true) (fun _ => a) (fun _ => b), ?_, ?_, ?_⟩
      · intro j hj; change Fin 3 at j; fin_cases j
        · rfl
        · rfl
        · exact (hj rfl).elim
      · intro j; exact Fin.elim0 j
      · exact ⟨fun _ h => hne (h x rfl), fun _ _ _ => rfl⟩
  · intro i; exact Fin.elim0 i

#print axioms guardedEqLegacy
#print axioms guardedEq_sensitivity

end D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrationTemplates
