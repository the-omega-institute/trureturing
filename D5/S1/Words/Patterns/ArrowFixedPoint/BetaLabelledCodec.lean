/- GID: D5/S1/Words/Patterns/ArrowFixedPoint/BetaLabelledCodec
   generality: I
   mirror-B: D5/B/S1/Words/Patterns/ArrowFixedPoint/BetaLabelledCodec
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Labelled final-cycle insertion data for beta avoidance. -/

import D5.S1.Words.Patterns.ArrowFixedPoint.BetaDecomposition
import D5.S1.Words.Patterns.ArrowFixedPoint.LabelPartition

/-!
# Beta labelled insertion

The selected low labels occupy the final cycle after its decreasing high
anchors.  The complementary low labels form the earlier derangement cycles.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Patterns.ArrowFixedPoint

open Equiv Equiv.Perm

noncomputable section

abbrev BetaSelected {n : ℕ} (m : Fin n) (chosen : Finset (Below m)) :=
  {x : Below m // x ∈ chosen}

abbrev BetaRemaining {n : ℕ} (m : Fin n) (chosen : Finset (Below m)) :=
  {x : Below m // x ∉ chosen}

/-- Separate the chosen low labels from their complement. -/
def betaLowPartition {n : ℕ} (m : Fin n) (chosen : Finset (Below m)) :
    Below m ≃ BetaRemaining m chosen ⊕ BetaSelected m chosen where
  toFun x := if hx : x ∈ chosen then Sum.inr ⟨x, hx⟩ else Sum.inl ⟨x, hx⟩
  invFun x := x.elim Subtype.val Subtype.val
  left_inv x := by
    dsimp
    split_ifs <;> rfl
  right_inv x := by
    rcases x with x | x
    · simp [x.2]
    · simp [x.2]

/-- Four disjoint label classes: earlier low, selected low, the singleton
`m`, and high. -/
def betaLabelPartition {n : ℕ} (m : Fin n) (chosen : Finset (Below m)) :
    Fin n ≃ BetaRemaining m chosen ⊕
      Option (BetaSelected m chosen ⊕ AboveIndex m) :=
  ((labelPartition m).trans
    (Equiv.sumCongr (betaLowPartition m chosen) (Equiv.refl _))).trans {
      toFun := fun x => match x with
        | Sum.inl (Sum.inl y) => Sum.inl y
        | Sum.inl (Sum.inr y) => Sum.inr (some (Sum.inl y))
        | Sum.inr none => Sum.inr none
        | Sum.inr (some y) => Sum.inr (some (Sum.inr y))
      invFun := fun x => match x with
        | Sum.inl y => Sum.inl (Sum.inl y)
        | Sum.inr none => Sum.inr none
        | Sum.inr (some (Sum.inl y)) => Sum.inl (Sum.inr y)
        | Sum.inr (some (Sum.inr y)) => Sum.inr (some y)
      left_inv := by
        intro x
        rcases x with (x | x)
        · cases x <;> rfl
        · cases x <;> rfl
      right_inv := by
        intro x
        rcases x with (x | x)
        · rfl
        · cases x with
          | none => rfl
          | some y => cases y <;> rfl
    }

/-- Complete labelled data for the `m<n` beta branch. -/
structure BetaLabelCode {n : ℕ} (m : Fin n) (_hm : m.val + 1 < n) where
  chosen : Finset (Below m)
  selected : CompleteWord (BetaSelected m chosen)
  slots : Slots (BetaSelected m chosen) selected.word (Fintype.card (Above m))
  delta : derangements (Fin (Fintype.card (BetaRemaining m chosen)))

namespace BetaLabelCode

variable {n : ℕ} {m : Fin n} {hm : m.val + 1 < n}

/-- Decreasing high labels, with the paper's largest label first. -/
def highDescending : List (AboveIndex m) :=
  Finset.univ.sort (fun x y : AboveIndex m => y ≤ x)

/-- The final cycle begins with a high label and has one following slot for
every high label, including the last one. -/
def finalPieces (code : BetaLabelCode m hm) :
    List (List (BetaSelected m code.chosen)) := [] :: code.slots.pieces

def finalWord (code : BetaLabelCode m hm) :
    CompleteWord (BetaSelected m code.chosen ⊕ AboveIndex m) :=
  completeWeave code.finalPieces (highDescending (m := m))
    (by simp [finalPieces, highDescending, code.slots.length_eq])
    (by simpa [finalPieces, code.slots.flatten_eq] using code.selected.nodup)
    (by simpa [finalPieces, code.slots.flatten_eq] using code.selected.complete)
    (Finset.sort_nodup _ _)
    (by intro x; simp [highDescending])

/-- The earlier cycles use only the unchosen labels and have no fixed point. -/
def earlierWord (code : BetaLabelCode m hm) :
    CompleteWord (BetaRemaining m code.chosen) :=
  (CompleteWord.ofPermutation (theta code.delta.1)).map
    (Fintype.orderIsoFinOfCardEq (BetaRemaining m code.chosen) rfl).toEquiv

def fullAnchors (code : BetaLabelCode m hm) :
    List (Option (BetaSelected m code.chosen ⊕ AboveIndex m)) :=
  none :: code.finalWord.word.map some

def fullPieces (code : BetaLabelCode m hm) :
    List (List (BetaRemaining m code.chosen)) :=
  code.earlierWord.word :: List.replicate code.fullAnchors.length []

def coloredWord (code : BetaLabelCode m hm) :
    CompleteWord (BetaRemaining m code.chosen ⊕
      Option (BetaSelected m code.chosen ⊕ AboveIndex m)) :=
  completeWeave code.fullPieces code.fullAnchors (by simp [fullPieces])
    (by simpa [fullPieces] using code.earlierWord.nodup)
    (by simpa [fullPieces] using code.earlierWord.complete)
    (by
      rw [fullAnchors, List.nodup_cons]
      exact ⟨by simp, code.finalWord.nodup.map (Option.some_injective _)⟩)
    (by
      intro x
      rcases x with _ | x
      · simp [fullAnchors]
      · simp only [fullAnchors, List.mem_cons, Option.some_ne_none, false_or,
          List.mem_map, Option.some.injEq]
        exact ⟨x, code.finalWord.complete x, rfl⟩)

/-- Actual one-line permutation from the complete beta label data. -/
def word (code : BetaLabelCode m hm) : CompleteWord (Fin n) :=
  code.coloredWord.map (betaLabelPartition m code.chosen).symm

def decode (code : BetaLabelCode m hm) : Equiv.Perm (Fin n) :=
  code.word.toPermutation

end BetaLabelCode

end

end D5.S1.Words.Patterns.ArrowFixedPoint
