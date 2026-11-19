import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.HuangCutParity
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonPlacements

/-! Relate the bitwise opposite-half count to parity on the cube. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoReconstruction

open private toggle from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoEmbeddingSearch
open private neighborMask from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonPlacements

private abbrev Vertex := BitVec 9

private theorem bit_insert (a n i : Nat) :
    (a ||| (1 <<< n)).testBit i = true ↔ a.testBit i = true ∨ n = i := by
  rw [Nat.testBit_or, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow,
    Bool.or_eq_true_iff, decide_eq_true_eq]

private theorem bit_fold_insert (axes : List (Fin 8)) (x : Vertex) (a i : Nat) :
    (axes.foldl (fun mask j => mask ||| (1 <<< ((toggle x j.succ).toNat / 2))) a).testBit i =
      true ↔ a.testBit i = true ∨ ∃ j ∈ axes, (toggle x j.succ).toNat / 2 = i := by
  induction axes generalizing a with
  | nil => simp
  | cons j axes ih =>
    simp only [List.foldl_cons, ih, bit_insert, List.mem_cons]
    constructor
    · rintro ((ha | hj) | ⟨k, hk, he⟩)
      · exact Or.inl ha
      · exact Or.inr ⟨j, Or.inl rfl, hj⟩
      · exact Or.inr ⟨k, Or.inr hk, he⟩
    · rintro (ha | ⟨k, hk | hk, he⟩)
      · exact Or.inl (Or.inl ha)
      · subst k
        exact Or.inl (Or.inr he)
      · exact Or.inr ⟨k, hk, he⟩

private theorem same_cut {x : Vertex} (h : x.getLsbD 0 = false) (i : Fin 8) :
    (toggle x i.succ).getLsbD 0 = false := by
  have hi : (i.succ : Fin 9).val ≠ 0 := by simp
  rw [toggle, BitVec.getLsbD_xor, h, BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
  simp [hi]

private theorem key_eq {x y : Vertex}
    (hx : x.getLsbD 0 = false) (hy : y.getLsbD 0 = false) :
    x.toNat / 2 = y.toNat / 2 ↔ x = y := by
  have h1 := Nat.mod_two_eq_zero_iff_testBit_zero.mpr hx
  have h2 := Nat.mod_two_eq_zero_iff_testBit_zero.mpr hy
  rw [← BitVec.toNat_inj]
  omega

private theorem neighborMask_bit {x y : Vertex}
    (hx : x.getLsbD 0 = false) (hy : y.getLsbD 0 = false) :
    (neighborMask x).testBit (y.toNat / 2) = true ↔
      x = y ∨ ∃ j : Fin 8, toggle x j.succ = y := by
  unfold neighborMask
  rw [bit_fold_insert, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow, decide_eq_true_eq]
  simp only [List.mem_finRange, true_and, key_eq hx hy, key_eq (same_cut hx _) hy]

private def bitValue (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem bitValue_xor (a b : Bool) : bitValue (a ^^ b) = bitValue a + bitValue b := by
  decide +revert

private theorem bit_fold_xor (half : List Vertex) (a i : Nat) :
    bitValue ((half.foldl (fun mask x => mask ^^^ neighborMask x) a).testBit i) =
      bitValue (a.testBit i) + (half.map fun x => bitValue ((neighborMask x).testBit i)).sum := by
  induction half generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_xor, bitValue_xor, List.map_cons,
      List.sum_cons, add_assoc]

/-- The bit used by the search is the sum modulo two of the contributions
from the occupied points in the closed in-plane neighborhood. -/
theorem reconstruction_bit (half : List Vertex) {y : Vertex}
    (hhalf : ∀ x ∈ half, x.getLsbD 0 = false) (hy : y.getLsbD 0 = false) :
    bitValue ((half.foldl (fun mask x => mask ^^^ neighborMask x) 0).testBit (y.toNat / 2)) =
      (half.map fun x => if x = y ∨ (∃ j : Fin 8, toggle x j.succ = y)
        then (1 : ZMod 2) else 0).sum := by
  rw [bit_fold_xor]
  simp only [Nat.zero_testBit, bitValue, Bool.false_eq_true, ite_false, zero_add]
  congr 1
  apply List.map_congr_left
  intro x hx
  simp only [neighborMask_bit (hhalf x hx) hy]

#print axioms reconstruction_bit

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoReconstruction
