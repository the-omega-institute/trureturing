/- GID: D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords
   mirror-E: none(waiver:no-computational-evidence)
   anchors: []
   utility: none
   digest: Canonical labelled membership words connect original-host visibility to full periodic forbidden-factor avoidance. -/

import D5.S3.Combinatorics.Graph.MutualVisibility.Andrasfai
import D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiLanguage
import Mathlib.Data.List.OfFn

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiWords

open Andrasfai AndrasfaiLanguage

private instance modulus_neZero (m : ℕ) : NeZero (3 * m + 2) := ⟨by omega⟩

/-- Labels retain the original vertex names and the fixed origin. -/
def membershipLabels (m : ℕ) (X : Finset (Vertex m)) (i : Fin (3*m+2)) : Bool :=
  decide ((i.val : Vertex m) ∈ X)

/-- The finite word lists the actual subset membership in increasing representative order. -/
def membershipWord (m : ℕ) (X : Finset (Vertex m)) : List Bool :=
  List.ofFn (membershipLabels m X)

/-- Recover an actual vertex subset from its Boolean labels. -/
def subsetOfLabels (m : ℕ) (b : Fin (3*m+2) → Bool) : Finset (Vertex m) :=
  Finset.univ.filter (fun v => b ⟨v.val, ZMod.val_lt v⟩ = true)

private theorem subset_labels_inverse (m : ℕ) (X : Finset (Vertex m)) :
    subsetOfLabels m (membershipLabels m X) = X := by
  ext v
  simp [subsetOfLabels, membershipLabels, ZMod.natCast_zmod_val]

private theorem labels_subset_inverse (m : ℕ) (b : Fin (3*m+2) → Bool) :
    membershipLabels m (subsetOfLabels m b) = b := by
  funext i
  simp [membershipLabels, subsetOfLabels, ZMod.val_natCast_of_lt i.isLt]

/-- A labelled subset and its full Boolean membership function are equivalent. -/
def subsetLabelsEquiv (m : ℕ) : Finset (Vertex m) ≃ (Fin (3*m+2) → Bool) where
  toFun := membershipLabels m
  invFun := subsetOfLabels m
  left_inv := subset_labels_inverse m
  right_inv := labels_subset_inverse m

/-- The membership word has the full original host order. -/
theorem membership_word_length (m : ℕ) (X : Finset (Vertex m)) :
    (membershipWord m X).length = 3*m+2 := by
  simp [membershipWord]

private theorem periodic_avoidance_replicate (w : List Bool) :
    PeriodicAvoidance w ↔ ∀ r, ¬ ContainsForbidden ((List.replicate r w).flatten) := by
  unfold PeriodicAvoidance
  apply forall_congr'
  intro r
  apply not_congr
  congr 1
  induction r with
  | zero => rfl
  | succ r ih =>
    change _ ++ w = _
    rw [List.replicate_succ', List.flatten_append, ih]
    simp

private theorem repeated_word (m : ℕ) (X : Finset (Vertex m)) (r : ℕ) :
    (List.replicate r (membershipWord m X)).flatten =
      List.ofFn (fun i : Fin (r*(3*m+2)) => decide ((i.val : Vertex m) ∈ X)) := by
  rw [membershipWord, ← List.ofFn_fin_repeat]
  congr 1
  funext i
  simp [Fin.repeat, Fin.modNat, membershipLabels, ZMod.natCast_mod]

end D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiWords
