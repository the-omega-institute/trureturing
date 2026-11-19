/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyTwoReconstruction
   generality: G
   mirror-B: none(waiver:covered-by-q9-twenty-two-paired-exclusion-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Identify the reconstructed bits with the occupied opposite coordinate slice. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CubeLayerDisjointness
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.HuangCutParity
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonCoverage

/-! Relate the bitwise opposite-half count to parity on the cube. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoReconstruction

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip flip_flip flip_adj)
open BalancedCubeLowerBound (coordinateSlice)
open private coordinate_slice_card_sum from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open HuangCutParity (halfParity mem_flip_iff_halfParity)
open private indicator from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.HuangCutParity
open private flip_direction_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeLayerDisjointness
open private toggle from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeBitMoves
open Q9TwentyTwoSingletonCoverage (candidate_size_ne_fifty)
open private candidates neighborMask reconstructionSize from
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

/-- The integer counted by the placement search is the cardinality of the
actual opposite half. -/
theorem reconstruction_size {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (half : List Vertex) (hn : half.Nodup)
    (hm : ∀ x : Vertex, x ∈ half ↔ cubeBitVec 9 x ∈ coordinateSlice C false) :
    reconstructionSize half = (coordinateSlice C true).card := by
  classical
  let e := cubeBitVec 9
  let mask := half.foldl (fun m x => m ^^^ neighborMask x) 0
  let T := (Finset.range 256).filter (fun i => mask.testBit i = true)
  have hcount : reconstructionSize half = T.card := by
    change (List.range 256).countP mask.testBit = _
    rw [List.countP_eq_length_filter,
      ← List.toFinset_card_of_nodup ((List.nodup_range (n := 256)).filter _),
      List.toFinset_filter]
    apply congrArg Finset.card
    apply Finset.ext
    intro i
    simp only [T, Finset.mem_filter, List.mem_toFinset, List.mem_range, Finset.mem_range]
  rw [hcount]
  have hplace (i : Nat) (hi : i < 256) :
      (BitVec.ofNat 9 (2 * i) : Vertex).toNat = 2 * i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hplane (i : Nat) (hi : i < 256) :
      (BitVec.ofNat 9 (2 * i) : Vertex).getLsbD 0 = false := by
    change (BitVec.ofNat 9 (2 * i)).toNat.testBit 0 = false
    exact Nat.mod_two_eq_zero_iff_testBit_zero.mp (by rw [hplace i hi]; omega)
  let f (i : Nat) := flip (e (BitVec.ofNat 9 (2 * i))) 0
  apply Finset.card_bij (fun i _ => f i)
  · intro i hi
    obtain ⟨hi, hb0⟩ := Finset.mem_filter.mp hi
    have hlt := Finset.mem_range.mp hi
    have hp := hplane i hlt
    have he := bit_iff_opposite_mem hr hb half hn hm hp
    rw [hplace i hlt, show 2 * i / 2 = i by omega] at he
    exact Finset.mem_filter.mpr ⟨he.mp hb0, by
      simp [f, show e (BitVec.ofNat 9 (2 * i)) 0 = false from hp]⟩
  · intro i hi j hj hij
    have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hjt := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hx := congrArg (fun z : Q 9 => flip z 0) hij
    change flip (flip (e (BitVec.ofNat 9 (2 * i))) 0) 0 =
      flip (flip (e (BitVec.ofNat 9 (2 * j))) 0) 0 at hx
    simp only [BalancedCriticalSpectrum.flip_flip] at hx
    have he := congrArg BitVec.toNat (e.injective hx)
    rw [hplace i hlt, hplace j hjt] at he
    omega
  · intro z hz
    obtain ⟨hzC, hz1⟩ := Finset.mem_filter.mp hz
    let y := e.symm (flip z 0)
    have he : e y = flip z 0 := e.apply_symm_apply _
    have hy : y.getLsbD 0 = false := by
      change e y 0 = false
      rw [he]
      simp [hz1]
    have hylt := y.isLt
    let i := y.toNat / 2
    have hi : i < 256 := by change 2 ^ 9 > y.toNat at hylt; dsimp [i]; omega
    have hi2 : 2 * i = y.toNat := by
      have hy0 := Nat.mod_two_eq_zero_iff_testBit_zero.mpr hy
      dsimp [i]
      omega
    have hy' : BitVec.ofNat 9 (2 * i) = y := by
      apply BitVec.toNat_inj.mp
      rw [hplace i hi, hi2]
    have hf : f i = z := by
      unfold f
      rw [hy', he, BalancedCriticalSpectrum.flip_flip]
    have hi1 : mask.testBit i = true := by
      apply (bit_iff_opposite_mem hr hb half hn hm hy).mpr
      rw [show cubeBitVec 9 y = flip z 0 from he, BalancedCriticalSpectrum.flip_flip]
      exact hzC
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hi1⟩, hf⟩

#print axioms reconstruction_size

/-- A half belonging to the normalized singleton-parity search cannot be the
22-point half of a balanced cubic support of order 72. -/
theorem no_listed_singleton_half {C : Finset (Q 9)} (hc : C.card = 72)
    (hs : (coordinateSlice C false).card = 22)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (half : List Vertex) (hn : half.Nodup)
    (hm : ∀ x : Vertex, x ∈ half ↔ cubeBitVec 9 x ∈ coordinateSlice C false)
    {opposite : Bool} (hp : half ∈ candidates opposite) : False := by
  have h := candidate_size_ne_fifty hp
  rw [reconstruction_size hr hb half hn hm] at h
  have hsum := coordinate_slice_card_sum C
  omega

#print axioms no_listed_singleton_half

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoReconstruction
