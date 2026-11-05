import D5.S3.Combinatorics.CircularWords.SingleDeletionFiberCount
import D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction

open D5.S3.Combinatorics.CircularWords
open CircularDeletionTransport CyclicInsertionGap SingleDeletionFiberCount
open DeletionReadoutReconstruction

set_option autoImplicit false
universe u
variable {α : Type u} [DecidableEq α]

noncomputable section

-- Canonical SupportedCircle/deletionReadout application of the reusable fibre theorem.
example {A : Finset α} (hA : 3 ≤ A.card) (x : A)
    (B : SupportedCircle (A.erase x.val)) :
    Nat.card {C : SupportedCircle A // deletionReadout A x C = B.val} = A.card - 1 := by
  let e : {C : SupportedCircle A // deletionReadout A x C = B.val} ≃
      {C : Cycle α // C.Nodup ∧ C.toFinset = A ∧ delete x.val C = B.val} :=
    { toFun := fun C => ⟨C.val.val, C.val.property.1, C.val.property.2, C.property⟩
      invFun := fun C => ⟨⟨C.val, C.property.1, C.property.2.1⟩, C.property.2.2⟩
      left_inv := fun C => rfl
      right_inv := fun C => rfl }
  exact (Nat.card_congr e).trans (deletion_fiber_card hA x.property B.property.1 B.property.2)

-- The reusable theorem specializes uniformly to every support size n ≥ 4.
example {A : Finset α} (hA : 4 ≤ A.card)
    {x : α} (hx : x ∈ A) {B : Cycle α} (hB : B.Nodup)
    (sB : B.toFinset = A.erase x) :
    Nat.card {C : Cycle α // C.Nodup ∧ C.toFinset = A ∧ delete x C = B} = A.card - 1 := by
  exact deletion_fiber_card (le_trans (by omega) hA) hx hB sB

-- The slot j = 0 is the cyclic cut and is included by gapCircle_fiber.
example {A : Finset α} {x : α} (hx : x ∈ A) {B : List α}
    (hB : B.Nodup) (hB0 : B ≠ []) (sB : B.toFinset = A.erase x) :
    (gapCircle B x (⟨0, List.length_pos_iff.mpr hB0⟩)).Nodup ∧
      x ∈ gapCircle B x (⟨0, List.length_pos_iff.mpr hB0⟩) ∧
      delete x (gapCircle B x (⟨0, List.length_pos_iff.mpr hB0⟩)) = (B : Cycle α) := by
  have h := (insertionEquiv hx hB hB0 sB ⟨0, List.length_pos_iff.mpr hB0⟩).property
  exact ⟨h.1, by simp [gapCircle], h.2.2⟩

example {A : Finset α} {x : α} (hx : x ∈ A) {B : List α}
    (hB : B.Nodup) (hB0 : B ≠ []) (sB : B.toFinset = A.erase x) :
    Fintype {C : Cycle α // C.Nodup ∧ C.toFinset = A ∧ delete x C = (B : Cycle α)} :=
  Fintype.ofEquiv (Fin B.length) (insertionEquiv hx hB hB0 sB)

#check @insertionEquiv
#check @deletion_fiber_card
#print axioms insertionEquiv
#print axioms deletion_fiber_card
