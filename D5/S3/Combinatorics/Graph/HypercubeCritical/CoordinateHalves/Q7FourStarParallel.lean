/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q7FourStarParallel
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q7FourStarParallel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Parallelism of four separated cubical stars with cancelling parity defects. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q7FourStarParity
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9OrbitCertificateProbe
import Mathlib.Algebra.BigOperators.Fin

/-! The four-star parallelism step for Hong–Wu–Xia, §7 Problem 2. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q7FourStarParallel

open Q7FourStarParity
open scoped BigOperators

/-- Relabel the bits of a mask, sending input coordinate `i` to `p i`. -/
def permuteBits {n : Nat} (p : Equiv.Perm (Fin n)) (x : BitVec n) : BitVec n :=
  (cubeBitVec n).symm (fun i => cubeBitVec n x (p.symm i))

private theorem permute_bit {n : Nat} (p : Equiv.Perm (Fin n)) (x : BitVec n) (i : Fin n) :
    (permuteBits p x).getLsbD i.val = x.getLsbD (p.symm i).val :=
  congrFun ((cubeBitVec n).apply_symm_apply _) i

private theorem zero_bit {n : Nat} (i : Nat) : (0 : BitVec n).getLsbD i = false :=
  BitVec.getLsbD_zero

private theorem permute_injective {n : Nat} (p : Equiv.Perm (Fin n)) :
    Function.Injective (permuteBits p) := by
  intro x y h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hbit := congrArg (fun b : BitVec n => b.getLsbD (p ⟨i, hi⟩).val) h
  simpa only [permute_bit, Equiv.symm_apply_apply] using hbit

private theorem permute_zero {n : Nat} (p : Equiv.Perm (Fin n)) :
    permuteBits p 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (permuteBits p 0).getLsbD (⟨i, hi⟩ : Fin n).val = _
  rw [permute_bit p 0 ⟨i, hi⟩, zero_bit, zero_bit]

private theorem permute_and {n : Nat} (p : Equiv.Perm (Fin n)) (x y : BitVec n) :
    permuteBits p (x &&& y) = permuteBits p x &&& permuteBits p y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (permuteBits p (x &&& y)).getLsbD (⟨i, hi⟩ : Fin n).val = _
  rw [permute_bit p (x &&& y) ⟨i, hi⟩, BitVec.getLsbD_and, BitVec.getLsbD_and,
    permute_bit p x ⟨i, hi⟩, permute_bit p y ⟨i, hi⟩]

private theorem permute_xor {n : Nat} (p : Equiv.Perm (Fin n)) (x y : BitVec n) :
    permuteBits p (x ^^^ y) = permuteBits p x ^^^ permuteBits p y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (permuteBits p (x ^^^ y)).getLsbD (⟨i, hi⟩ : Fin n).val = _
  rw [permute_bit p (x ^^^ y) ⟨i, hi⟩, BitVec.getLsbD_xor, BitVec.getLsbD_xor,
    permute_bit p x ⟨i, hi⟩, permute_bit p y ⟨i, hi⟩]

private theorem cpopNatRec_eq_sum {n : Nat} (x : BitVec n) (m : Nat) :
    x.cpopNatRec m 0 = ∑ i : Fin m, (x.getLsbD i.val).toNat := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [BitVec.cpopNatRec_succ, Nat.zero_add, BitVec.cpopNatRec_eq, ih,
      Fin.sum_univ_castSucc]
    rfl

private theorem cpop_permute {n : Nat} (p : Equiv.Perm (Fin n)) (x : BitVec n) :
    (permuteBits p x).cpop = x.cpop := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_cpop, cpopNatRec_eq_sum, permute_bit]
  exact Equiv.sum_comp p.symm (fun i => (x.getLsbD i.val).toNat)

private def support {n : Nat} (x : BitVec n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x.getLsbD i.val = true)

private theorem card_support {n : Nat} (x : BitVec n) :
    (support x).card = x.cpop.toNat := by
  rw [BitVec.toNat_cpop, cpopNatRec_eq_sum]
  rw [Finset.card_eq_sum_ite (Finset.subset_univ (support x))]
  apply Finset.sum_congr rfl
  intro i _
  cases hb : x.getLsbD i.val <;>
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, hb,
      Bool.false_eq_true, ite_false, ite_true] <;> rfl

private abbrev axisBit (i : Fin 7) : BitVec 7 := BitVec.ofNat 7 (2 ^ i.val)

private theorem axis_bit (i j : Fin 7) :
    (axisBit j).getLsbD i.val = decide (i = j) := by
  rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
  simp [i.isLt, Fin.ext_iff, eq_comm]

private theorem permute_axis (p : Equiv.Perm (Fin 7)) (i : Fin 7) :
    permuteBits p (axisBit i) = axisBit (p i) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let k : Fin 7 := ⟨j, hj⟩
  change (permuteBits p (axisBit i)).getLsbD k.val = (axisBit (p i)).getLsbD k.val
  rw [permute_bit, axis_bit, axis_bit]
  simp only [Equiv.symm_apply_eq]

private theorem axis_unused (a : BitVec 7) (i : Fin 7) :
    a &&& axisBit i = 0 ↔ a.getLsbD i.val = false := by
  constructor
  · intro h
    have hi := congrArg (fun b : BitVec 7 => b.getLsbD i.val) h
    simpa only [BitVec.getLsbD_and, axis_bit, decide_true, Bool.and_true,
      zero_bit] using hi
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let k : Fin 7 := ⟨j, hj⟩
    change (a &&& axisBit i).getLsbD k.val = _
    rw [BitVec.getLsbD_and, axis_bit, zero_bit]
    by_cases hki : k = i
    · simp only [hki, h, decide_true, Bool.and_true]
    · simp only [hki, decide_false, Bool.and_false]

private abbrev vertexBit (v : BitVec 7) : BitVec 128 := (1 : BitVec 128) <<< v.toNat

private theorem vertex_bit (x v : BitVec 7) :
    (vertexBit v).getLsbD x.toNat = true ↔ x = v := by
  change ((1#128) <<< v.toNat).getLsbD x.toNat = true ↔ _
  rw [BitVec.getLsbD_shiftLeft]
  have hx : x.toNat < 128 := x.isLt
  simp only [hx, decide_true, Bool.true_and, BitVec.getLsbD_one, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  constructor
  · intro h
    exact BitVec.eq_of_toNat_eq (by omega)
  · rintro rfl
    simp

private theorem fold_or_bit {α : Type} (xs : List α) (skip : α → Prop)
    [DecidablePred skip] (mask : α → BitVec 128) (start : BitVec 128) (i : Nat) :
    (xs.foldl (fun acc d => if skip d then acc else acc ||| mask d) start).getLsbD i = true ↔
      start.getLsbD i = true ∨ ∃ d ∈ xs, ¬ skip d ∧ (mask d).getLsbD i = true := by
  induction xs generalizing start with
  | nil => simp
  | cons d xs ih =>
    rw [List.foldl_cons, ih]
    by_cases h : skip d
    · simp [h]
    · simp [h, BitVec.getLsbD_or, or_assoc]

private theorem fold_or_bit_of_take {α : Type} (xs : List α) (take : α → Prop)
    [DecidablePred take] (mask : α → BitVec 128) (start : BitVec 128) (i : Nat) :
    (xs.foldl (fun acc d => if take d then acc ||| mask d else acc) start).getLsbD i = true ↔
      start.getLsbD i = true ∨ ∃ d ∈ xs, take d ∧ (mask d).getLsbD i = true := by
  simpa only [ite_not, not_not] using fold_or_bit xs (fun d => ¬ take d) mask start i

private abbrev axisList : List (Fin 7) := List.finRange 7

-- This is the fold in starDefect, indexed by coordinates.
private theorem defect_fold (c a : BitVec 7) :
    starDefect c a = axisList.foldl
      (fun acc i => if a &&& axisBit i = 0 then
        acc ||| axisList.foldl
          (fun leaves j => if a &&& axisBit j = 0 then leaves else
            leaves ||| vertexBit (c ^^^ axisBit i ^^^ axisBit j))
          (vertexBit (c ^^^ axisBit i))
      else acc) 0 := by
  rfl

private theorem defect_bit (c a x : BitVec 7) :
    (starDefect c a).getLsbD x.toNat = true ↔
      ∃ i : Fin 7, a.getLsbD i.val = false ∧
        (x = c ^^^ axisBit i ∨
          ∃ j : Fin 7, a.getLsbD j.val = true ∧ x = c ^^^ axisBit i ^^^ axisBit j) := by
  rw [defect_fold, fold_or_bit_of_take]
  simp only [zero_bit, Bool.false_eq_true, false_or, List.mem_finRange, true_and, axis_unused]
  simp only [fold_or_bit, vertex_bit, List.mem_finRange, true_and, Bool.not_eq_false]


private def vertexLabels : BitVec 7 ≃ Fin 128 where
  toFun := BitVec.toFin
  invFun := BitVec.ofFin (w := 7)
  left_inv := BitVec.ofFin_toFin (w := 7)
  right_inv := BitVec.toFin_ofFin (w := 7)

private def vertexPerm (e : Equiv.Perm (BitVec 7)) : Equiv.Perm (Fin 128) :=
  vertexLabels.symm.trans (e.trans vertexLabels)

private theorem permute_vertex_bit (e : Equiv.Perm (BitVec 7)) (b : BitVec 128) (x : BitVec 7) :
    (permuteBits (vertexPerm e) b).getLsbD (e x).toNat = b.getLsbD x.toNat := by
  have h := permute_bit (vertexPerm e) b (vertexLabels (e x))
  have hlabel : (vertexPerm e).symm (vertexLabels (e x)) = vertexLabels x := by
    apply (vertexPerm e).injective
    simp [vertexPerm]
  rw [hlabel] at h
  exact h

private theorem eq_of_vertex_bits {x y : BitVec 128}
    (h : ∀ v : BitVec 7, x.getLsbD v.toNat = y.getLsbD v.toNat) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact h (BitVec.ofFin ⟨i, hi⟩)

private def coordPerm (p : Equiv.Perm (Fin 7)) : Equiv.Perm (BitVec 7) :=
  (cubeBitVec 7).trans ((Equiv.arrowCongr p (Equiv.refl Bool)).trans (cubeBitVec 7).symm)

private theorem defect_permute (p : Equiv.Perm (Fin 7)) (c a : BitVec 7) :
    permuteBits (vertexPerm (coordPerm p)) (starDefect c a) =
      starDefect (permuteBits p c) (permuteBits p a) := by
  apply eq_of_vertex_bits
  intro y
  obtain ⟨x, rfl⟩ := (coordPerm p).surjective y
  rw [permute_vertex_bit]
  change (starDefect c a).getLsbD x.toNat =
    (starDefect (permuteBits p c) (permuteBits p a)).getLsbD (permuteBits p x).toNat
  apply Bool.eq_iff_iff.mpr
  simp only [defect_bit, permute_bit]
  have map_single (i : Fin 7) :
      permuteBits p (c ^^^ axisBit i) = permuteBits p c ^^^ axisBit (p i) := by
    rw [permute_xor, permute_axis]
  have map_double (i j : Fin 7) :
      permuteBits p (c ^^^ axisBit i ^^^ axisBit j) =
        permuteBits p c ^^^ axisBit (p i) ^^^ axisBit (p j) := by
    rw [permute_xor, map_single, permute_axis]
  constructor
  · rintro ⟨i, hi, h | ⟨j, hj, h⟩⟩
    · exact ⟨p i, by simpa only [Equiv.symm_apply_apply], Or.inl (map_single i ▸ congrArg _ h)⟩
    · exact ⟨p i, by simpa only [Equiv.symm_apply_apply], Or.inr
        ⟨p j, by simpa only [Equiv.symm_apply_apply], map_double i j ▸ congrArg _ h⟩⟩
  · rintro ⟨i, hi, h | ⟨j, hj, h⟩⟩
    · refine ⟨p.symm i, hi, Or.inl (permute_injective p ?_)⟩
      simpa only [map_single, Equiv.apply_symm_apply] using h
    · refine ⟨p.symm i, hi, Or.inr ⟨p.symm j, hj, permute_injective p ?_⟩⟩
      simpa only [map_double, Equiv.apply_symm_apply] using h

private def translate (c : BitVec 7) : Equiv.Perm (BitVec 7) where
  toFun x := c ^^^ x
  invFun x := c ^^^ x
  left_inv x := by
    change c ^^^ (c ^^^ x) = x
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  right_inv x := by
    change c ^^^ (c ^^^ x) = x
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

private theorem defect_translate (c a : BitVec 7) :
    permuteBits (vertexPerm (translate c)) (starDefect 0 a) = starDefect c a := by
  apply eq_of_vertex_bits
  intro y
  obtain ⟨x, rfl⟩ := (translate c).surjective y
  rw [permute_vertex_bit]
  change (starDefect 0#7 a).getLsbD x.toNat = (starDefect c a).getLsbD (c ^^^ x).toNat
  apply Bool.eq_iff_iff.mpr
  have cancel (u v : BitVec 7) : c ^^^ u = c ^^^ v ↔ u = v :=
    (translate c).apply_eq_iff_eq
  simp only [defect_bit, BitVec.zero_xor, BitVec.xor_assoc, cancel]

set_option maxRecDepth 4096 in
private theorem defect_origin_card (i : Fin 128) :
    let a : BitVec 7 := BitVec.ofFin i
    a.cpop = 3 → (starDefect 0 a).cpop = 16 := by
  have h : ∀ j : Fin 128, (BitVec.ofFin j : BitVec 7).cpop = 3 →
      (starDefect 0 (BitVec.ofFin j)).cpop = 16 := by decide +kernel
  exact h i

private theorem defect_card (c a : BitVec 7) (ha : a.cpop = 3) :
    (starDefect c a).cpop = 16 := by
  rw [← defect_translate, cpop_permute]
  exact defect_origin_card a.toFin ha

private theorem support_and {n : Nat} (u v : BitVec n) :
    support (u &&& v) = support u ∩ support v := by
  ext i
  simp [support]

private theorem root_cover_bound {u v w : BitVec 128}
    (h : starDefect 0 7 ^^^ u ^^^ v ^^^ w = 0) :
    16 ≤ (starDefect 0 7 &&& u).cpop.toNat +
      (starDefect 0 7 &&& v).cpop.toNat + (starDefect 0 7 &&& w).cpop.toNat := by
  let root := support (starDefect 0 7)
  rw [← card_support, ← card_support, ← card_support, support_and, support_and, support_and]
  have cover : root ⊆ (root ∩ support u) ∪ (root ∩ support v) ∪ (root ∩ support w) := by
    intro i hi
    have hroot : (starDefect 0 7).getLsbD i.val = true := (Finset.mem_filter.mp hi).2
    have hpar := congrArg (fun b : BitVec 128 => b.getLsbD i.val) h
    simp only [BitVec.getLsbD_xor, zero_bit, hroot] at hpar
    simp only [Finset.mem_union, Finset.mem_inter, hi, true_and, support, Finset.mem_filter,
      Finset.mem_univ]
    by_contra hnone
    simp only [not_or, Bool.not_eq_true] at hnone
    rw [hnone.1.1, hnone.1.2, hnone.2] at hpar
    contradiction
  have hroot : root.card = 16 := by
    rw [card_support, defect_card 0 7 (by decide)]
    decide
  have hsub := Finset.card_le_card cover
  have h₁ := Finset.card_union_le (root ∩ support u) (root ∩ support v)
  have h₂ := Finset.card_union_le ((root ∩ support u) ∪ (root ∩ support v)) (root ∩ support w)
  change 16 ≤ (root ∩ support u).card + (root ∩ support v).card + (root ∩ support w).card
  omega

-- Fill the designated coordinates by swapping within each block of root or
-- nonroot coordinates. Earlier positions in the same block stay fixed.
private def moveTo (p : Equiv.Perm (Fin 7)) (target : Fin 7) (mask : BitVec 7) :
    Equiv.Perm (Fin 7) :=
  let source := (axisList.find? fun i =>
    decide (target ≤ i ∧ (i.val < 3 ↔ target.val < 3)) &&
      mask.getLsbD (p.symm i).val).getD target
  p.trans (Equiv.swap source target)

private def normalize (c a : BitVec 7) : Equiv.Perm (Fin 7) :=
  let p := Equiv.refl (Fin 7)
  let p := moveTo p 0 a
  let p := moveTo p 1 a
  let p := moveTo p 3 c
  let p := moveTo p 4 c
  moveTo p 5 a

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the permitted axis masks for the six possible second centers.
private theorem normalization_checked (i : Fin 128) :
    let c : BitVec 7 := BitVec.ofFin i
    c.cpop = 2 ∧ c &&& 7 = 0 →
      ∀ j : Fin 128,
        let a : BitVec 7 := BitVec.ofFin j
        a.cpop = 3 →
        (a = 7 ∨ (a &&& 7).cpop = 2 ∧ a &&& c = 0) →
          permuteBits (normalize c a) 7 = 7 ∧
          permuteBits (normalize c a) c = 24 ∧
          (permuteBits (normalize c a) a = 7 ∨ permuteBits (normalize c a) a = 35) := by
  have h : (List.finRange 128).all (fun k =>
      let c : BitVec 7 := BitVec.ofFin k
      if c.cpop = 2 ∧ c &&& 7 = 0 then (List.finRange 128).all (fun j =>
        let a : BitVec 7 := BitVec.ofFin j
        decide (a.cpop = 3 → (a = 7 ∨ (a &&& 7).cpop = 2 ∧ a &&& c = 0) →
          permuteBits (normalize c a) 7 = 7 ∧ permuteBits (normalize c a) c = 24 ∧
          (permuteBits (normalize c a) a = 7 ∨ permuteBits (normalize c a) a = 35)))
      else true) = true := by decide +kernel
  dsimp only
  intro hc j
  have hi := List.all_eq_true.mp h i (List.mem_finRange _)
  rw [ite_eq_left hc] at hi
  exact of_decide_eq_true (List.all_eq_true.mp hi j (List.mem_finRange _))


private theorem normalized_residual_parallel {a c b d e : BitVec 7}
    (hb : b.cpop = 3) (he : e.cpop = 3) (hc0 : c ≠ 0) (hc24 : c ≠ 24)
    (ha : a = 7 ∨ a = 35)
    (hpar : starDefect 0 7 ^^^ starDefect 24 a ^^^ starDefect c b ^^^ starDefect d e = 0) :
    a = 7 ∧ b = 7 ∧ c &&& 7 = 0 := by
  have hres : residual a c b = starDefect d e := by
    apply BitVec.xor_eq_zero_iff.mp
    exact hpar
  have hcard : (residual a c b).cpop = 16 := hres ▸ defect_card d e he
  rcases ha with rfl | rfl
  · obtain ⟨rfl, hc⟩ := (parallel_residual_card_eq_sixteen_iff hb hc0 hc24).mp hcard
    refine ⟨rfl, rfl, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact (nonparallel_residual_card_ne_sixteen hb hc0 hc24 hcard).elim

private theorem xor_swap_last (r u v w : BitVec 128) :
    r ^^^ u ^^^ v ^^^ w = r ^^^ u ^^^ w ^^^ v := by
  rw [BitVec.xor_assoc (r ^^^ u), BitVec.xor_comm v w, ← BitVec.xor_assoc]

private theorem xor_swap_middle (r u v w : BitVec 128) :
    r ^^^ u ^^^ v ^^^ w = r ^^^ v ^^^ u ^^^ w := by
  rw [BitVec.xor_assoc r, BitVec.xor_comm u v, ← BitVec.xor_assoc]

private theorem parallel_of_large_overlap {c a d b e f : BitVec 7}
    (ha : a.cpop = 3) (hb : b.cpop = 3) (hf : f.cpop = 3)
    (hd0 : d ≠ 0) (he0 : e ≠ 0) (hdc : d ≠ c) (hec : e ≠ c)
    (hshape : c.cpop = 2 ∧ c &&& 7 = 0 ∧
      (a = 7 ∨ (a &&& 7).cpop = 2 ∧ a &&& c = 0))
    (hpar : starDefect 0 7 ^^^ starDefect c a ^^^ starDefect d b ^^^ starDefect e f = 0) :
    (a = 7 ∧ c &&& 7 = 0) ∧ (b = 7 ∧ d &&& 7 = 0) ∧ (f = 7 ∧ e &&& 7 = 0) := by
  let p := normalize c a
  obtain ⟨hp, hpc, hpa⟩ :=
    normalization_checked c.toFin ⟨hshape.1, hshape.2.1⟩ a.toFin ha hshape.2.2
  change permuteBits p 7 = 7 at hp
  change permuteBits p c = 24 at hpc
  change permuteBits p a = 7 ∨ permuteBits p a = 35 at hpa
  have hperm := congrArg (permuteBits (vertexPerm (coordPerm p))) hpar
  simp only [permute_xor, permute_zero, defect_permute, hp, hpc] at hperm
  have hdp0 : permuteBits p d ≠ 0 := by
    rw [← permute_zero p]
    exact fun h => hd0 (permute_injective p h)
  have hep0 : permuteBits p e ≠ 0 := by
    rw [← permute_zero p]
    exact fun h => he0 (permute_injective p h)
  have hdp24 : permuteBits p d ≠ 24 := by
    rw [← hpc]
    exact fun h => hdc (permute_injective p h)
  have hep24 : permuteBits p e ≠ 24 := by
    rw [← hpc]
    exact fun h => hec (permute_injective p h)
  have hbp : (permuteBits p b).cpop = 3 := (cpop_permute p b).trans hb
  have hfp : (permuteBits p f).cpop = 3 := (cpop_permute p f).trans hf
  obtain ⟨ha', hb', hd'⟩ := normalized_residual_parallel hbp hfp hdp0 hdp24 hpa hperm
  rw [xor_swap_last] at hperm
  obtain ⟨_, hf', he'⟩ := normalized_residual_parallel hfp hbp hep0 hep24 hpa hperm
  have pull_axes {u : BitVec 7} (h : permuteBits p u = 7) : u = 7 :=
    permute_injective p (h.trans hp.symm)
  have pull_center {u : BitVec 7} (h : permuteBits p u &&& 7 = 0) : u &&& 7 = 0 :=
    permute_injective p (by rw [permute_and, hp, h, permute_zero])
  exact ⟨⟨pull_axes ha', hshape.2.1⟩, ⟨pull_axes hb', pull_center hd'⟩,
    ⟨pull_axes hf', pull_center he'⟩⟩

/-- With the first star at center `0` and axes `7` (coordinates 0, 1 and 2),
cancelling defects force the same axes on all four stars and zero center bits
in those axes. Separation from the first star and distinct centers suffice. -/
theorem four_star_parallel {c₁ c₂ c₃ a₁ a₂ a₃ : BitVec 7}
    (ha₁ : a₁.cpop = 3) (ha₂ : a₂.cpop = 3) (ha₃ : a₃.cpop = 3)
    (hs₁ : separatedFromRoot c₁ a₁ = true) (hs₂ : separatedFromRoot c₂ a₂ = true)
    (hs₃ : separatedFromRoot c₃ a₃ = true)
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hc₃ : c₃ ≠ 0)
    (hc₁₂ : c₁ ≠ c₂) (hc₁₃ : c₁ ≠ c₃) (hc₂₃ : c₂ ≠ c₃)
    (hpar : starDefect 0 7 ^^^ starDefect c₁ a₁ ^^^ starDefect c₂ a₂ ^^^
      starDefect c₃ a₃ = 0) :
    (a₁ = 7 ∧ c₁ &&& 7 = 0) ∧ (a₂ = 7 ∧ c₂ &&& 7 = 0) ∧ (a₃ = 7 ∧ c₃ &&& 7 = 0) := by
  obtain ⟨he₁, hshape₁⟩ := root_defect_overlap_classification ha₁ hs₁
  obtain ⟨he₂, hshape₂⟩ := root_defect_overlap_classification ha₂ hs₂
  obtain ⟨he₃, hshape₃⟩ := root_defect_overlap_classification ha₃ hs₃
  have hcover := root_cover_bound hpar
  change 16 ≤ rootDefectOverlap c₁ a₁ + rootDefectOverlap c₂ a₂ +
    rootDefectOverlap c₃ a₃ at hcover
  have hlarge : 6 ≤ rootDefectOverlap c₁ a₁ ∨ 6 ≤ rootDefectOverlap c₂ a₂ ∨
      6 ≤ rootDefectOverlap c₃ a₃ := by omega
  rcases hlarge with h₁ | h₂ | h₃
  · exact parallel_of_large_overlap ha₁ ha₂ ha₃ hc₂ hc₃ hc₁₂.symm hc₁₃.symm (hshape₁ h₁) hpar
  · rw [xor_swap_middle] at hpar
    obtain ⟨h₂', h₁', h₃'⟩ :=
      parallel_of_large_overlap ha₂ ha₁ ha₃ hc₁ hc₃ hc₁₂ hc₂₃.symm (hshape₂ h₂) hpar
    exact ⟨h₁', h₂', h₃'⟩
  · rw [xor_swap_last, xor_swap_middle] at hpar
    obtain ⟨h₃', h₁', h₂'⟩ :=
      parallel_of_large_overlap ha₃ ha₁ ha₂ hc₁ hc₂ hc₁₃ hc₂₃ (hshape₃ h₃) hpar
    exact ⟨h₁', h₂', h₃'⟩

#print axioms four_star_parallel

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q7FourStarParallel
