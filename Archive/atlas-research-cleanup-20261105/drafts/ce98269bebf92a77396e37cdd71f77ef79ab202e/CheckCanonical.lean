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
    (gapCircle B x (⟨0, by simpa using hB0⟩)).Nodup ∧
      x ∈ gapCircle B x (⟨0, by simpa using hB0⟩) ∧
      delete x (gapCircle B x (⟨0, by simpa using hB0⟩)) = (B : Cycle α) := by
  have hxB : x ∉ B := by
    intro h
    have : x ∈ A.erase x := sB ▸ List.mem_toFinset.mpr h
    exact (Finset.mem_erase.mp this).1 rfl
  let j0 : Fin B.length := ⟨0, by simpa using hB0⟩
  refine (gapCircle_fiber hB hB0 hxB (gapCircle B x j0)).mpr ?_
  refine ⟨j0, rfl, ?_⟩
  intro k hk
  have he : B.rotate k.val = B.rotate j0.val :=
    anchored_coe_injective (by
      simpa [gapCircle] using
        (List.nodup_cons.mpr ⟨by simpa using hxB, List.nodup_rotate.mpr hB⟩))
      hk.symm
  apply Fin.ext
  simpa only [Nat.mod_eq_of_lt k.isLt, Nat.mod_eq_of_lt j0.isLt]
    using hB.rotate_congr hB0 k.val j0.val he

example {A : Finset α} {x : α} (hx : x ∈ A) {B : List α}
    (hB : B.Nodup) (hB0 : B ≠ []) (sB : B.toFinset = A.erase x) :
    Fintype {C : Cycle α // C.Nodup ∧ C.toFinset = A ∧ delete x C = (B : Cycle α)} :=
  Fintype.ofEquiv (Fin B.length) (insertionEquiv hx hB hB0 sB)

#check @insertionEquiv
#check @deletion_fiber_card
#print axioms insertionEquiv
#print axioms deletion_fiber_card
