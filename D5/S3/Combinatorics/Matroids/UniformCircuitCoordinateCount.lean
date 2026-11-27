/- GID: D5/S3/Combinatorics/Matroids/UniformCircuitCoordinateCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/UniformCircuitCoordinateCount
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Count subset coordinates using insertion and deletion of two designated elements. -/

module

public import Mathlib.Data.Set.PowersetCard

/-! Coordinate counts for the split of the uniform circuit equations. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.UniformCircuitCoordinateCount

open Finset
open Set.powersetCard (card_eq)
set_option autoImplicit false

variable {I : Type*} [DecidableEq I] {k : ℕ}

def avoidBoth (i j : I) : I → Prop := fun x => x ≠ i ∧ x ≠ j

instance (i j : I) : DecidablePred (avoidBoth i j) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Subsets avoiding two chosen elements can be read as subsets of their complement. -/
def avoidBothEquiv (i j : I) (r : ℕ) :
    {F : Set.powersetCard I r // i ∉ F ∧ j ∉ F} ≃ Set.powersetCard (Subtype (avoidBoth i j)) r where
  toFun F :=
    ⟨F.val.val.subtype (avoidBoth i j), by
      change (F.val.val.subtype (avoidBoth i j)).card = r
      rw [← card_map (Function.Embedding.subtype (avoidBoth i j)),
        subtype_map_of_mem (fun x hx => ⟨fun e => F.prop.1 (e ▸ hx), fun e => F.prop.2 (e ▸ hx)⟩)]
      exact F.val.prop⟩
  invFun F := ⟨⟨F.val.map (Function.Embedding.subtype (avoidBoth i j)), by
      change (F.val.map _).card = r
      rw [card_map]
      exact F.prop⟩,
      ⟨notMem_map_subtype_of_not_property _ (fun h => h.1 rfl),
       notMem_map_subtype_of_not_property _ (fun h => h.2 rfl)⟩⟩
  left_inv F := by
    apply Subtype.ext
    apply Subtype.ext
    exact subtype_map_of_mem (fun x hx => ⟨fun e => F.prop.1 (e ▸ hx), fun e => F.prop.2 (e ▸ hx)⟩)
  right_inv F := by
    apply Subtype.ext
    ext x
    simp only [mem_subtype, mem_map, Function.Embedding.subtype_apply]
    exact ⟨fun ⟨y, hy, heq⟩ => Subtype.ext heq ▸ hy, fun h => ⟨x, h, rfl⟩⟩

/-- Removing the specified nonpivot element gives a subset one size smaller. -/
def removeSpecifiedEquiv (i j : I) (h : i ≠ j) (r : ℕ) :
    {F : Set.powersetCard I (r + 1) // i ∉ F ∧ j ∈ F} ≃
      {F : Set.powersetCard I r // i ∉ F ∧ j ∉ F} where
  toFun F := ⟨⟨F.val.val.erase j, by
      change (F.val.val.erase j).card = r
      rw [card_erase_of_mem F.prop.2, card_eq, Nat.add_sub_cancel]⟩,
      ⟨fun k => F.prop.1 (mem_of_mem_erase k), notMem_erase _ _⟩⟩
  invFun F := ⟨⟨insert j F.val.val, by
      change (insert j F.val.val).card = r + 1
      rw [card_insert_of_notMem F.prop.2, card_eq]⟩,
      ⟨fun k => (mem_insert.mp k).elim h F.prop.1, mem_insert_self _ _⟩⟩
  left_inv F := by
    apply Subtype.ext
    apply Subtype.ext
    exact insert_erase F.prop.2
  right_inv F := by
    apply Subtype.ext
    apply Subtype.ext
    exact erase_insert F.prop.2

/-- The available subsets avoiding two distinguished elements are counted by
the binomial coefficient of their complement. -/
theorem card_avoid_both [Fintype I] (i j : I) (h : i ≠ j) (r : ℕ) :
    Nat.card {F : Set.powersetCard I r // i ∉ F ∧ j ∉ F} =
      (Fintype.card I - 2).choose r := by
  classical
  rw [Nat.card_congr (avoidBothEquiv i j r), Set.powersetCard.card]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have heq : (univ.filter (avoidBoth i j) : Finset I) = univ \ {i, j} := by
    ext x
    simp [avoidBoth, not_or]
  rw [heq, card_sdiff_of_subset (subset_univ _), card_univ, card_pair h]

/-- If the nonpivot must appear, its deletion gives one fewer free choice. -/
theorem card_include_nonpivot [Fintype I] (i j : I) (h : i ≠ j) (r : ℕ) :
    Nat.card {F : Set.powersetCard I (r + 1) // i ∉ F ∧ j ∈ F} =
      (Fintype.card I - 2).choose r := by
  rw [Nat.card_congr (removeSpecifiedEquiv i j h r), card_avoid_both i j h]

end D5.S3.Combinatorics.Matroids.UniformCircuitCoordinateCount
