/- GID: D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/TotalUnimodularL1Repair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: L1 rounding and modular support bounds for totally unimodular integer matrices. -/

import D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.ZMod.Basic

/-!
# Integral repair for totally unimodular matrices

Split a real solution into nonnegative positive and negative parts. A kernel
direction on the current support allows a step that removes a coordinate
without increasing the sum. When the restricted matrix has trivial kernel,
its integer inner inverse recovers the restricted solution over the integers.
The resulting integer repair also gives a support bound after reduction to
any `ZMod n`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open scoped BigOperators

namespace D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair

variable {M N : Type*}

/-- The finite set of indices where a vector is nonzero. -/
noncomputable def nonzeroSupport {K : Type*} [Zero K] [Fintype N]
    (w : N → K) : Finset N := by
  classical
  exact Finset.univ.filter fun j => w j ≠ 0

@[simp] theorem mem_nonzeroSupport {K : Type*} [Zero K] [Fintype N]
    {w : N → K} {j : N} : j ∈ nonzeroSupport w ↔ w j ≠ 0 := by
  classical
  simp [nonzeroSupport]

/-- The two signed copies of each column preserve total unimodularity. -/
theorem fromCols_neg_isTotallyUnimodular (A : Matrix M N ℤ)
    (hA : A.IsTotallyUnimodular) : (Matrix.fromCols A (-A)).IsTotallyUnimodular := by
  classical
  rw [Matrix.isTotallyUnimodular_iff]
  intro k rows cols
  let underlying : N ⊕ N → N := Sum.elim id id
  let signs : Fin k → SignType := fun j => Sum.elim (fun _ => 1) (fun _ => -1) (cols j)
  let U := A.submatrix rows (underlying ∘ cols)
  have hU : U.det ∈ Set.range (SignType.cast : SignType → ℤ) :=
    (Matrix.isTotallyUnimodular_iff A).mp hA k rows (underlying ∘ cols)
  obtain ⟨s, hs⟩ := hU
  have hminor : (Matrix.fromCols A (-A)).submatrix rows cols =
      Matrix.of (fun i j => (signs j : ℤ) * U i j) := by
    ext i j
    cases hcol : cols j <;>
      simp [signs, U, underlying, hcol, SignType.coe_one]
  refine ⟨(∏ j, signs j) * s, ?_⟩
  rw [hminor, Matrix.det_mul_row, ← hs, SignType.coe_mul]
  exact congrArg (fun c : ℤ => c * (s : ℤ))
    (map_prod (SignType.castHom : SignType →*₀ ℤ) signs Finset.univ)

private theorem fromCols_neg_mulVec {K : Type*} [Ring K] [Fintype N]
    (A : Matrix M N K) (w : N ⊕ N → K) :
    Matrix.fromCols A (-A) *ᵥ w = A *ᵥ (fun j => w (.inl j) - w (.inr j)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromCols_apply_inl,
    Matrix.fromCols_apply_inr, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib,
    mul_sub, Finset.sum_sub_distrib]
  rw [sub_eq_add_neg]

private noncomputable def extendByZero {K : Type*} [Zero K] (s : Finset N)
    (v : s → K) : N → K := by
  classical
  exact fun j => if hj : j ∈ s then v ⟨j, hj⟩ else 0

private theorem mulVec_extendByZero [Fintype N] (A : Matrix M N ℝ)
    (s : Finset N) (v : s → ℝ) :
    A.submatrix id (fun j : s => j.val) *ᵥ v = A *ᵥ extendByZero s v := by
  classical
  funext i
  change (∑ j : s, A i j * v j) = ∑ j : N, A i j * extendByZero s v j
  calc
    (∑ j : s, A i j * v j) = ∑ j : s, A i j * extendByZero s v j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [extendByZero, dite_eq_left j.property]
    _ = ∑ j ∈ s, A i j * extendByZero s v j :=
      Finset.sum_coe_sort s (fun j => A i j * extendByZero s v j)
    _ = ∑ j : N, A i j * extendByZero s v j := by
      refine Finset.sum_subset (Finset.subset_univ s) fun j _ hj => ?_
      simp [extendByZero, hj]

/-- A nonzero kernel direction supported on a nonnegative vector gives a
feasible step that removes a coordinate and does not increase the sum. -/
private theorem eliminate_support_coordinate [Fintype N] (A : Matrix M N ℝ)
    (w d : N → ℝ) (hw : ∀ j, 0 ≤ w j) (hd : A *ᵥ d = 0) (hdne : d ≠ 0)
    (hdsupp : ∀ j, w j = 0 → d j = 0) :
    ∃ y : N → ℝ, (∀ j, 0 ≤ y j) ∧ A *ᵥ y = A *ᵥ w ∧
      (∑ j, y j) ≤ (∑ j, w j) ∧ (nonzeroSupport y).card < (nonzeroSupport w).card := by
  classical
  obtain ⟨a, ha, hane, hasupp, hacost⟩ :
      ∃ a : N → ℝ, A *ᵥ a = 0 ∧ a ≠ 0 ∧
        (∀ j, w j = 0 → a j = 0) ∧ (∑ j, a j) ≤ 0 := by
    by_cases h : (∑ j, d j) ≤ 0
    · exact ⟨d, hd, hdne, hdsupp, h⟩
    · refine ⟨-d, ?_, ?_, ?_, ?_⟩
      · rw [Matrix.mulVec_neg, hd, neg_zero]
      · exact neg_ne_zero.mpr hdne
      · intro j hj
        change -d j = 0
        rw [hdsupp j hj, neg_zero]
      · simp only [Pi.neg_apply, Finset.sum_neg_distrib]
        exact neg_nonpos.mpr (le_of_lt (lt_of_not_ge h))
  obtain ⟨j₀, hj₀⟩ : ∃ j, a j < 0 := by
    by_contra hnegative
    have hnonneg (j : N) : 0 ≤ a j := le_of_not_gt fun hj => hnegative ⟨j, hj⟩
    have hsum : (∑ j, a j) = 0 :=
      le_antisymm hacost (Finset.sum_nonneg fun j _ => hnonneg j)
    apply hane
    funext j
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp hsum j
      (Finset.mem_univ j)
  let negative := Finset.univ.filter fun j => a j < 0
  have hnegative : negative.Nonempty := ⟨j₀, by simp [negative, hj₀]⟩
  let ratio : N → ℝ := fun j => w j / (-a j)
  obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image negative ratio hnegative
  have hak : a k < 0 := by
    simpa only [negative, Finset.mem_filter, Finset.mem_univ, true_and] using hk
  have hwk : 0 < w k := lt_of_le_of_ne (hw k) (fun h =>
    (ne_of_lt hak) (hasupp k h.symm))
  let t := ratio k
  have ht : 0 < t := div_pos hwk (neg_pos.mpr hak)
  let y : N → ℝ := w + t • a
  refine ⟨y, ?_, ?_, ?_, ?_⟩
  · intro j
    change 0 ≤ w j + t * a j
    by_cases hj : a j < 0
    · have hmul : t * (-a j) ≤ w j :=
        (le_div_iff₀ (neg_pos.mpr hj)).mp (hmin j (by simp [negative, hj]))
      calc
        0 ≤ w j - t * (-a j) := sub_nonneg.mpr hmul
        _ = w j + t * a j := by rw [mul_neg, sub_neg_eq_add]
    · exact add_nonneg (hw j) (mul_nonneg ht.le (le_of_not_gt hj))
  · dsimp only [y]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, ha, smul_zero, add_zero]
  · change (∑ j, (w j + t * a j)) ≤ (∑ j, w j)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos ht.le hacost)
  · have hsubset : nonzeroSupport y ⊆ nonzeroSupport w := by
      intro j hj
      apply mem_nonzeroSupport.mpr
      intro hjzero
      apply mem_nonzeroSupport.mp hj
      change w j + t * a j = 0
      rw [hjzero, hasupp j hjzero, mul_zero, add_zero]
    have hyk : y k = 0 := by
      have hmul : t * (-a k) = w k := div_mul_cancel₀ _ (ne_of_gt (neg_pos.mpr hak))
      calc
        y k = w k - t * (-a k) := by
          change w k + t * a k = _
          rw [mul_neg, sub_neg_eq_add]
        _ = 0 := sub_eq_zero.mpr hmul.symm
    apply Finset.card_lt_card
    exact (Finset.ssubset_iff_of_subset hsubset).mpr
      ⟨k, mem_nonzeroSupport.mpr (ne_of_gt hwk), fun h => (mem_nonzeroSupport.mp h) hyk⟩

/-- An integral inner inverse recovers the unique solution on independent columns. -/
private theorem integer_solution_of_kernel_zero [Fintype M] [Fintype N]
    (A : Matrix M N ℤ) (hA : A.IsTotallyUnimodular) (b : M → ℤ) (v : N → ℝ)
    (hsol : A.map (Int.castRingHom ℝ) *ᵥ v = fun i => (b i : ℝ))
    (hker : ∀ d : N → ℝ, A.map (Int.castRingHom ℝ) *ᵥ d = 0 → d = 0) :
    ∃ z : N → ℤ, ∀ j, (z j : ℝ) = v j := by
  classical
  obtain ⟨B, hB⟩ :=
    D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.exists_integer_inner_inverse A hA
  let f := Int.castRingHom ℝ
  have hB' : A.map f * B.map f * A.map f = A.map f := by
    simpa only [Matrix.map_mul] using congrArg (fun T => T.map f) hB
  let z := B *ᵥ b
  have hzmap : (fun j => (z j : ℝ)) = B.map f *ᵥ (fun i => (b i : ℝ)) := by
    funext j
    exact f.map_mulVec B b j
  have hz : A.map f *ᵥ (fun j => (z j : ℝ)) = fun i => (b i : ℝ) := by
    rw [hzmap, ← hsol, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hB', hsol]
  have hd := hker ((fun j => (z j : ℝ)) - v) (by
    rw [Matrix.mulVec_sub, hz, hsol, sub_self])
  exact ⟨z, fun j => sub_eq_zero.mp (congrFun hd j)⟩

private theorem exists_nonnegative_integer_repair [Fintype M] [Fintype N]
    (A : Matrix M N ℤ) (hA : A.IsTotallyUnimodular) (b : M → ℤ) (w : N → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hsol : A.map (Int.castRingHom ℝ) *ᵥ w = fun i => (b i : ℝ)) :
    ∃ z : N → ℤ, (∀ j, 0 ≤ z j) ∧ A *ᵥ z = b ∧ (∑ j, (z j : ℝ)) ≤ ∑ j, w j := by
  classical
  let f := Int.castRingHom ℝ
  let Aℝ := A.map f
  suffices ∀ (k : ℕ) (u : N → ℝ), (nonzeroSupport u).card = k →
      (∀ j, 0 ≤ u j) → (Aℝ *ᵥ u = fun i => (b i : ℝ)) →
      ∃ z : N → ℤ, (∀ j, 0 ≤ z j) ∧ A *ᵥ z = b ∧ (∑ j, (z j : ℝ)) ≤ ∑ j, u j from
    this _ w rfl hw hsol
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro u hcard hu husol
    let s := nonzeroSupport u
    let C : Matrix M s ℤ := A.submatrix id (fun j : s => j.val)
    have hmul (v : s → ℝ) : C.map f *ᵥ v = Aℝ *ᵥ extendByZero s v :=
      mulVec_extendByZero Aℝ s v
    by_cases hdep : ∃ d : s → ℝ, C.map f *ᵥ d = 0 ∧ d ≠ 0
    · obtain ⟨d, hd, hdne⟩ := hdep
      let e := extendByZero s d
      have he : Aℝ *ᵥ e = 0 := (hmul d).symm.trans hd
      have hene : e ≠ 0 := by
        intro hezero
        apply hdne
        funext j
        have hj := congrFun hezero j.val
        simpa [e, extendByZero, j.property] using hj
      have hesupp (j : N) (hj : u j = 0) : e j = 0 := by
        have hnot : j ∉ s := fun h => (mem_nonzeroSupport.mp h) hj
        simp [e, extendByZero, hnot]
      obtain ⟨y, hynonneg, hysol, hycost, hycard⟩ :=
        eliminate_support_coordinate Aℝ u e hu he hene hesupp
      obtain ⟨z, hznonneg, hzsol, hzcost⟩ :=
        ih _ (hycard.trans_eq hcard) y rfl hynonneg (hysol.trans husol)
      exact ⟨z, hznonneg, hzsol, hzcost.trans hycost⟩
    · have hker (d : s → ℝ) (hd : C.map f *ᵥ d = 0) : d = 0 := by
        by_contra hdne
        exact hdep ⟨d, hd, hdne⟩
      let v : s → ℝ := fun j => u j.val
      have hvext : extendByZero s v = u := by
        funext j
        by_cases hj : j ∈ s
        · simp [extendByZero, v, hj]
        · have hz : u j = 0 := by
            by_contra hne
            exact hj (mem_nonzeroSupport.mpr hne)
          simp [extendByZero, hj, hz]
      have hvsol : C.map f *ᵥ v = fun i => (b i : ℝ) := by
        rw [hmul v, hvext, husol]
      obtain ⟨zs, hzs⟩ :=
        integer_solution_of_kernel_zero C (hA.submatrix id (fun j : s => j.val))
          b v hvsol hker
      let z := extendByZero s zs
      have hzcast (j : N) : (z j : ℝ) = u j := by
        rw [← hvext]
        by_cases hj : j ∈ s
        · simpa only [z, extendByZero, dite_eq_left hj] using hzs ⟨j, hj⟩
        · simp only [z, extendByZero, dite_eq_right hj, Int.cast_zero]
      refine ⟨z, ?_, ?_, ?_⟩
      · intro j
        apply (Int.cast_nonneg_iff (R := ℝ)).mp
        rw [hzcast j]
        exact hu j
      · funext i
        apply (Int.cast_injective (α := ℝ))
        calc
          ((A *ᵥ z) i : ℝ) = (Aℝ *ᵥ (fun j => (z j : ℝ))) i := f.map_mulVec A z i
          _ = (Aℝ *ᵥ u) i := congrArg (fun q : N → ℝ => (Aℝ *ᵥ q) i) (funext hzcast)
          _ = (b i : ℝ) := congrFun husol i
      · exact le_of_eq (Finset.sum_congr rfl fun j _ => hzcast j)

/-- A real solution with integral right-hand side admits an integral repair
whose sum of absolute values is at most that of the given real solution. -/
theorem exists_integer_l1_repair [Fintype M] [Fintype N]
    (A : Matrix M N ℤ) (hA : A.IsTotallyUnimodular) (b : M → ℤ) (x : N → ℝ)
    (hsol : A.map (Int.castRingHom ℝ) *ᵥ x = fun i => (b i : ℝ)) :
    ∃ z : N → ℤ, A *ᵥ z = b ∧ (∑ j, |(z j : ℝ)|) ≤ ∑ j, |x j| := by
  classical
  let w : N ⊕ N → ℝ := Sum.elim (fun j => max (x j) 0) (fun j => max (-x j) 0)
  have hw (j : N ⊕ N) : 0 ≤ w j := by
    cases j <;> exact le_max_right _ _
  have hparts (j : N) :
      w (.inl j) - w (.inr j) = x j ∧ w (.inl j) + w (.inr j) = |x j| := by
    change max (x j) 0 - max (-x j) 0 = x j ∧ max (x j) 0 + max (-x j) 0 = |x j|
    rcases le_total 0 (x j) with hj | hj
    · simp [max_eq_left hj, max_eq_right (neg_nonpos.mpr hj), abs_of_nonneg hj]
    · simp [max_eq_right hj, max_eq_left (neg_nonneg.mpr hj), abs_of_nonpos hj]
  have hwcost : (∑ j, w j) = ∑ j, |x j| := by
    rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => (hparts j).2
  let C := Matrix.fromCols A (-A)
  let f := Int.castRingHom ℝ
  have hmap : C.map f = Matrix.fromCols (A.map f) (-(A.map f)) := by
    change (Matrix.fromCols A (-A)).map f = _
    rw [Matrix.fromCols_map]
    ext i j
    cases j <;> simp only [Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
      Matrix.map_apply, Matrix.neg_apply, map_neg]
  have hwsub : (fun j : N => w (.inl j) - w (.inr j)) = x :=
    funext fun j => (hparts j).1
  have hwsol : C.map f *ᵥ w = fun i => (b i : ℝ) := by
    rw [hmap, fromCols_neg_mulVec, hwsub]
    exact hsol
  obtain ⟨v, hvnonneg, hvsol, hvcost⟩ :=
    exists_nonnegative_integer_repair C (fromCols_neg_isTotallyUnimodular A hA) b w hw hwsol
  let z : N → ℤ := fun j => v (.inl j) - v (.inr j)
  refine ⟨z, ?_, ?_⟩
  · change Matrix.fromCols A (-A) *ᵥ v = b at hvsol
    simpa only [fromCols_neg_mulVec] using hvsol
  · calc
      (∑ j, |(z j : ℝ)|) ≤ ∑ j : N, ((v (.inl j) : ℝ) + (v (.inr j) : ℝ)) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hleft : (0 : ℝ) ≤ v (.inl j) := Int.cast_nonneg (hvnonneg (.inl j))
        have hright : (0 : ℝ) ≤ v (.inr j) := Int.cast_nonneg (hvnonneg (.inr j))
        dsimp only [z]
        rw [Int.cast_sub]
        simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hleft, abs_of_nonneg hright]
          using abs_sub_le (v (.inl j) : ℝ) 0 (v (.inr j) : ℝ)
      _ = ∑ j : N ⊕ N, (v j : ℝ) := by
        rw [Fintype.sum_sum_type, Finset.sum_add_distrib]
      _ ≤ ∑ j, |x j| := hvcost.trans_eq hwcost

/-- Each nonzero integer coordinate contributes at least one to the l1 cost. -/
theorem support_card_le_sum_abs [Fintype N] (z : N → ℤ) :
    ((nonzeroSupport z).card : ℝ) ≤ ∑ j, |(z j : ℝ)| := by
  classical
  calc
    ((nonzeroSupport z).card : ℝ) = ∑ j ∈ nonzeroSupport z, (1 : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ j ∈ nonzeroSupport z, |(z j : ℝ)| := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hone := Int.one_le_abs (mem_nonzeroSupport.mp hj)
      simpa only [Int.cast_one, Int.cast_abs] using (Int.cast_le (R := ℝ)).mpr hone
    _ ≤ ∑ j, |(z j : ℝ)| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _

/-- Reduction preserves the equation and can only shrink the support. -/
theorem reduce_integer_solution [Fintype N] (A : Matrix M N ℤ) (b : M → ℤ)
    (z : N → ℤ) (hz : A *ᵥ z = b) (n : ℕ) :
    (A.map (Int.castRingHom (ZMod n)) *ᵥ (fun j => (z j : ZMod n)) = fun i => (b i : ZMod n)) ∧
      nonzeroSupport (fun j => (z j : ZMod n)) ⊆ nonzeroSupport z := by
  constructor
  · funext i
    let f := Int.castRingHom (ZMod n)
    exact (f.map_mulVec A z i).symm.trans (congrArg f (congrFun hz i))
  · intro j hj
    apply mem_nonzeroSupport.mpr
    intro hzero
    exact (mem_nonzeroSupport.mp hj) (by simp [hzero])

/-- Reducing the integer repair bounds the modular support by the real l1 cost. -/
theorem exists_zmod_repair_with_support_bound [Fintype M] [Fintype N]
    (A : Matrix M N ℤ) (hA : A.IsTotallyUnimodular) (b : M → ℤ) (x : N → ℝ)
    (hsol : A.map (Int.castRingHom ℝ) *ᵥ x = fun i => (b i : ℝ)) (n : ℕ) :
    ∃ y : N → ZMod n, (A.map (Int.castRingHom (ZMod n)) *ᵥ y = fun i => (b i : ZMod n)) ∧
      ((nonzeroSupport y).card : ℝ) ≤ ∑ j, |x j| := by
  obtain ⟨z, hz, hcost⟩ := exists_integer_l1_repair A hA b x hsol
  obtain ⟨hy, hsubset⟩ := reduce_integer_solution A b z hz n
  have hcard := (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_card hsubset)
  exact ⟨fun j => (z j : ZMod n), hy, hcard.trans ((support_card_le_sum_abs z).trans hcost)⟩

end D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair
