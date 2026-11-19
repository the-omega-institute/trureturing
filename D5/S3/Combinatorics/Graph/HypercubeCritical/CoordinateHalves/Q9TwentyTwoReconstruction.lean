import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.HuangCutParity
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonPlacements

/-! Relate the bitwise opposite-half count to parity on the cube. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoReconstruction

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip flip_flip flip_adj)
open BalancedCubeLowerBound (coordinateSlice)
open HuangCutParity (halfParity mem_flip_iff_halfParity)
open private indicator from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.HuangCutParity
open private flip_direction_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeLayerDisjointness
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
  simp

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

private def localPoint (y : Q 9) (i : Fin 9) : Q 9 :=
  if i = 0 then y else flip y i

private theorem localPoint_injective (y : Q 9) : Function.Injective (localPoint y) := by
  intro i j hij
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · exact hi.trans hj.symm
  · exact ((flip_adj y j).ne (by simpa [localPoint, hi, hj] using hij)).elim
  · exact ((flip_adj y i).ne (by simpa [localPoint, hi, hj] using hij.symm)).elim
  · exact flip_direction_injective y (by simpa [localPoint, hi, hj] using hij)

private theorem halfParity_sum (S : Finset (Q 9)) (y : Q 9) :
    halfParity S y = ∑ i : Fin 9, indicator S (localPoint y i) := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin 9))]
  unfold halfParity
  rw [add_comm]
  congr 1

private theorem sum_list_of_nodup (xs : List Vertex) (nd : xs.Nodup) (f : Vertex → ZMod 2) :
    (xs.map f).sum = ∑ x ∈ xs.toFinset, f x := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have h := List.nodup_cons.mp nd
    simp [Finset.sum_insert, h.1, ih h.2]

attribute [local instance] Classical.propDecidable

/-- The reconstruction bits coincide with occupancy across the coordinate
cut for any enumeration of the actual first half without repetition. -/
theorem bit_iff_opposite_mem {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (half : List Vertex) (hn : half.Nodup)
    (hm : ∀ x : Vertex, x ∈ half ↔ cubeBitVec 9 x ∈ coordinateSlice C false)
    {y : Vertex} (hy : y.getLsbD 0 = false) :
    ((half.foldl (fun mask x => mask ^^^ neighborMask x) 0).testBit (y.toNat / 2)) =
      true ↔ flip (cubeBitVec 9 y) 0 ∈ C := by
  classical
  let e := cubeBitVec 9
  let S := coordinateSlice C false
  have hplane (x : Vertex) (hx : x ∈ half) : x.getLsbD 0 = false :=
    (Finset.mem_filter.mp ((hm x).mp hx)).2
  have hind (z : Q 9) :
      indicator S z = ∑ x ∈ half.toFinset, if e x = z then (1 : ZMod 2) else 0 := by
    rw [Finset.sum_boole]
    have he : half.toFinset.filter (fun x => e x = z) =
        if z ∈ S then {e.symm z} else ∅ := by
      ext x
      by_cases hz : z ∈ S
      · simp only [hz, ite_true, Finset.mem_singleton, Finset.mem_filter, List.mem_toFinset]
        constructor
        · exact fun h => e.injective (h.2.trans (e.apply_symm_apply z).symm)
        · rintro rfl
          exact ⟨(hm _).mpr (by simpa [e] using hz), e.apply_symm_apply z⟩
      · simp only [hz, ite_false, Finset.notMem_empty, Finset.mem_filter, List.mem_toFinset,
          iff_false]
        exact fun h => hz (h.2 ▸ (hm x).mp h.1)
    rw [he]
    by_cases hz : z ∈ S <;> simp [indicator, hz]
  have hclosed (x : Vertex) :
      (x = y ∨ ∃ j : Fin 8, toggle x j.succ = y) ↔
        ∃ i : Fin 9, e x = localPoint (e y) i := by
    have hj (j : Fin 8) :
        toggle x j.succ = y ↔ e x = flip (e y) j.succ := by
      rw [← e.injective.eq_iff, show e (toggle x j.succ) = flip (e x) j.succ
        from cubeBitVec_xor_single x j.succ]
      constructor
      · intro h
        rw [← h, BalancedCriticalSpectrum.flip_flip]
      · intro h
        rw [h, BalancedCriticalSpectrum.flip_flip]
    constructor
    · rintro (rfl | ⟨j, hjx⟩)
      · exact ⟨0, by simp [localPoint]⟩
      · exact ⟨j.succ, by simpa [localPoint] using (hj j).mp hjx⟩
    · rintro ⟨i, hi⟩
      refine Fin.cases ?_ (fun j h => Or.inr ⟨j, (hj j).mpr (by simpa [localPoint] using h)⟩)
        i hi
      exact fun h => Or.inl (e.injective (by simpa [localPoint] using h))
  have hp : halfParity S (e y) =
      (half.map fun x => if x = y ∨ (∃ j : Fin 8, toggle x j.succ = y)
        then (1 : ZMod 2) else 0).sum := by
    rw [halfParity_sum, sum_list_of_nodup half hn]
    simp only [hind]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    simp only [hclosed x, Finset.sum_boole]
    by_cases hx : ∃ i : Fin 9, e x = localPoint (e y) i
    · obtain ⟨i, hi⟩ := hx
      have he : Finset.univ.filter (fun j : Fin 9 => e x = localPoint (e y) j) = {i} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        rw [hi]
        exact ⟨fun h => (localPoint_injective (e y) h).symm, fun h => h ▸ rfl⟩
      simp [he, show ∃ j : Fin 9, e x = localPoint (e y) j from ⟨i, hi⟩]
    · have he : Finset.univ.filter (fun j : Fin 9 => e x = localPoint (e y) j) = ∅ := by
        exact Finset.filter_false_of_mem fun i _ h => hx ⟨i, h⟩
      simp [he, hx]
  rw [mem_flip_iff_halfParity hr hb (show e y 0 = false from hy), hp,
    ← reconstruction_bit half hplane hy]
  cases h : (half.foldl (fun mask x => mask ^^^ neighborMask x) 0).testBit (y.toNat / 2) <;>
    simp [bitValue]

#print axioms bit_iff_opposite_mem

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoReconstruction
