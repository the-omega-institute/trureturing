/- GID: D5/S3/Quantum/Analysis/RefinedBMVIntervalKernel
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Order, mathlib/module/Mathlib.Analysis.Calculus.Deriv.MeanValue]
   utility: none
   digest: Finite interval decomposition for the unrestricted refined BMV kernel. -/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Matrix.Order

/-! # Interval decomposition of the extreme kernel

For the three-letter refined BMV argument, the kernel on the upper triangle
is extended symmetrically. Ordered rectangle increments give nonnegative
coefficients of the rank-one matrices supported on sample intervals.
-/

open Finset Set
open scoped BigOperators ComplexOrder

noncomputable section

namespace RefinedBMV.IntervalKernel

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A finite array truncated at an outer row and column has a PSD symmetric extension
when the adjacent upper-triangular rectangle increments are nonnegative.
Interior entries of the array have indices `1, …, n`, with endpoints `0, n+1`. -/
theorem posSemidef_truncation {n : ℕ} (A : ℕ → ℕ → ℝ)
    (hrect : ∀ i j : ℕ, i ≤ j → j < n →
      0 ≤ (A (i + 1) (j + 1) - A i (j + 1)) - (A (i + 1) (j + 2) - A i (j + 2))) :
    (Matrix.of fun i j : Fin n ↦
      ((A (min i.val j.val + 1) (max i.val j.val + 1) - A 0 (max i.val j.val + 1) -
        (A (min i.val j.val + 1) (n + 1) - A 0 (n + 1)) : ℝ) : 𝕜)).PosSemidef := by
  let c (i j : ℕ) :=
    (A (i + 1) (j + 1) - A i (j + 1)) - (A (i + 1) (j + 2) - A i (j + 2))
  let indices := ((range n) ×ˢ (range n)).filter fun p : ℕ × ℕ ↦ p.1 ≤ p.2
  let v (p : ℕ × ℕ) (i : Fin n) : 𝕜 := if p.1 ≤ i.val ∧ i.val ≤ p.2 then 1 else 0
  let M (p : ℕ × ℕ) := c p.1 p.2 • Matrix.vecMulVec (v p) (star (v p))
  have hPSD : (∑ p ∈ indices, M p).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro p hp
    have hp' := mem_filter.mp hp
    exact (Matrix.posSemidef_vecMulVec_self_star (v p)).smul
      (hrect p.1 p.2 hp'.2 (mem_range.mp (mem_product.mp hp'.1).2))
  convert hPSD using 1
  ext i j
  let r := min i.val j.val
  let s := max i.val j.val
  have hrs : r ≤ s := (min_le_left _ _).trans (le_max_left _ _)
  have hs : s < n := max_lt_iff.mpr ⟨i.isLt, j.isLt⟩
  let included := (range (r + 1)) ×ˢ (Finset.Ico s n)
  have hsubset : included ⊆ indices := by
    intro p hp
    have hp₁ : p.1 ≤ r := Nat.lt_succ_iff.mp (mem_range.mp (mem_product.mp hp).1)
    have hp₂ := Finset.mem_Ico.mp (mem_product.mp hp).2
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr hp₂.2⟩,
      by omega⟩
  have hmem (p : ℕ × ℕ) (hp : p ∈ indices) :
      p ∈ included ↔ (p.1 ≤ i.val ∧ i.val ≤ p.2) ∧ (p.1 ≤ j.val ∧ j.val ≤ p.2) := by
    have hp₂ := mem_range.mp (mem_product.mp (mem_filter.mp hp).1).2
    simp only [included, mem_product, Finset.mem_Ico, Finset.mem_range, r, s, Nat.lt_succ_iff,
      le_min_iff, max_le_iff]
    tauto
  have hzero (p : ℕ × ℕ) (hp : p ∈ indices) (hp' : p ∉ included) : M p i j = 0 := by
    rw [hmem p hp] at hp'
    rw [not_and_or] at hp'
    simp only [M, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    rcases hp' with hi | hj
    · simp [v, hi]
    · simp [v, hj]
  have hone (p : ℕ × ℕ) (hp : p ∈ included) : M p i j = ((c p.1 p.2 : ℝ) : 𝕜) := by
    obtain ⟨hi, hj⟩ := (hmem p (hsubset hp)).mp hp
    simp only [M, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    simp [v, hi, hj, Algebra.smul_def, RCLike.algebraMap_eq_ofReal]
  simp only [Matrix.of_apply, Matrix.sum_apply]
  rw [← sum_subset hsubset hzero, sum_congr rfl hone]
  rw [← map_sum (algebraMap ℝ 𝕜)]
  congr 1
  rw [sum_product]
  have htel (f : ℕ → ℝ) : (∑ q ∈ Finset.Ico s n, (f q - f (q + 1))) = f s - f n := by
    calc
      _ = -(∑ q ∈ Finset.Ico s n, (f (q + 1) - f q)) := by
        rw [← sum_neg_distrib]
        simp only [neg_sub]
      _ = _ := by rw [sum_Ico_sub f hs.le, neg_sub]
  symm
  calc
    _ = ∑ p ∈ range (r + 1), ((A (p + 1) (s + 1) - A p (s + 1)) -
        (A (p + 1) (n + 1) - A p (n + 1))) :=
      sum_congr rfl fun p _ ↦ htel (fun q ↦ A (p + 1) (q + 1) - A p (q + 1))
    _ = _ := by
      rw [sum_sub_distrib, sum_range_sub (fun p ↦ A p (s + 1)),
        sum_range_sub (fun p ↦ A p (n + 1))]

/-- A nonpositive mixed derivative gives nonnegative ordered rectangle increments,
including rectangles whose upper-left sample interval ends on the diagonal. -/
theorem rectangle_nonneg_of_mixed_deriv_nonpos {a : ℝ} {K D : ℝ → ℝ → ℝ}
    (hc : ∀ y > a, ContinuousOn (fun x ↦ K x y) (Ioc a y))
    (hx : ∀ x y, a < x → x < y → HasDerivAt (fun t ↦ K t y) (D x y) x)
    (hy : ∀ x y, a < x → x < y → DifferentiableAt ℝ (D x) y ∧ deriv (D x) y ≤ 0)
    {l u v w : ℝ} (hal : a < l) (hlu : l ≤ u) (huv : u ≤ v) (hvw : v ≤ w) :
    0 ≤ (K u v - K l v) - (K u w - K l w) := by
  have hsubset {y : ℝ} (huy : u ≤ y) : Icc l u ⊆ Ioc a y :=
    fun _ ht ↦ ⟨hal.trans_le ht.1, ht.2.trans huy⟩
  have hleft (t) (ht : t ∈ interior (Icc l u)) :
      HasDerivAt (fun x ↦ K x v - K x w) (D t v - D t w) t := by
    rw [interior_Icc] at ht
    exact (hx t v (hal.trans ht.1) (ht.2.trans_le huv)).sub
      (hx t w (hal.trans ht.1) (ht.2.trans_le (huv.trans hvw)))
  have hmono : MonotoneOn (fun t ↦ K t v - K t w) (Icc l u) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc l u)
      (((hc v (hal.trans_le (hlu.trans huv))).mono (hsubset huv)).sub
        ((hc w (hal.trans_le (hlu.trans (huv.trans hvw)))).mono (hsubset (huv.trans hvw))))
      (fun t ht ↦ (hleft t ht).hasDerivWithinAt) ?_
    intro t ht
    rw [interior_Icc] at ht
    have hdiff (y) (h : y ∈ Icc v w) := hy t y (hal.trans ht.1) (ht.2.trans_le (huv.trans h.1))
    have hanti : AntitoneOn (D t) (Icc v w) :=
      antitoneOn_of_deriv_nonpos (convex_Icc v w)
        (fun y h ↦ (hdiff y h).1.continuousAt.continuousWithinAt)
        (fun y h ↦ (hdiff y (interior_subset h)).1.differentiableWithinAt)
        (fun y h ↦ (hdiff y (interior_subset h)).2)
    exact sub_nonneg.mpr (hanti ⟨le_rfl, hvw⟩ ⟨hvw, le_rfl⟩ hvw)
  have h := hmono ⟨le_rfl, hlu⟩ ⟨hlu, le_rfl⟩ hlu
  linarith only [h]

end RefinedBMV.IntervalKernel
