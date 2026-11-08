/- GID: D5/S3/Arith/Robin/ForwardKernel/FiniteProductMomentBounds
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/FiniteProductMomentBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourth moments control finite products and their telescoping replacement errors on probability spaces. -/

import D5.S3.Arith.Robin.ForwardKernel.MomentTransfer
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

namespace D5.S3.Arith.Robin.ForwardKernel.FiniteProductMomentBounds

open MeasureTheory Filter
open scoped BigOperators ENNReal

noncomputable section
set_option autoImplicit false

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {k : ℕ}

/-- A product of k functions in Lk is integrable for positive k. -/
lemma product_integrable (hk : 0 < k) {f : Fin k → α → ℝ}
    (hf : ∀ i, MemLp (f i) (k : ℝ≥0∞) μ) :
    Integrable (fun x => ∏ i, f i x) μ := by
  have h := MemLp.fun_prod (s := Finset.univ) (fun i _ => hf i)
  have he : (∑ _i : Fin k, (k : ℝ≥0∞)⁻¹)⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [ENNReal.mul_inv_cancel (by exact_mod_cast hk.ne') (by simp)]
    simp
  rw [he] at h
  exact memLp_one_iff_integrable.mp h

private lemma product_lpNorm_bound (hk : 0 < k) {f : Fin k → α → ℝ}
    (hf : ∀ i, MemLp (f i) (k : ℝ≥0∞) μ) :
    (∫ x, |∏ i, f i x| ∂μ) ≤ ∏ i, lpNorm (f i) (k : ℝ≥0∞) μ := by
  have hi (i : Fin k) : Integrable (fun x => |f i x| ^ k) μ := by
    simpa only [Real.norm_eq_abs] using (hf i).integrable_norm_pow hk.ne'
  have hp : Integrable (fun x => ∏ i, |f i x|) μ := by
    simpa only [Finset.abs_prod] using (product_integrable hk hf).abs
  have h := MomentTransfer.product_moment_bound hk
    (fun i => integral_nonneg (fun x => pow_nonneg (abs_nonneg _) _))
    (fun i => (hf i).aestronglyMeasurable) hi hp (fun _ => le_rfl)
  simpa only [Finset.abs_prod] using h.trans_eq (by
    congr 1
    funext i
    rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) (by simp)
      (hf i).aestronglyMeasurable]
    simp [Real.norm_eq_abs, Real.rpow_natCast, one_div])

private lemma fourth_lpNorm_le {f : α → ℝ} {C : ℝ}
    (hf : MemLp f 4 μ) (hb : (∫ x, |f x| ^ 4 ∂μ) ≤ C) :
    lpNorm f 4 μ ≤ C ^ (1 / 4 : ℝ) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    hf.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat, Real.norm_eq_abs]
  exact Real.rpow_le_rpow (integral_nonneg (fun _ => pow_nonneg (abs_nonneg _) _)) hb
    (by norm_num)

/-- On a probability space, fourth moment bounds control products of at most four factors. -/
theorem product_fourth_bound [IsProbabilityMeasure μ] (hk : 0 < k) (hk4 : k ≤ 4)
    {f : Fin k → α → ℝ} {C : Fin k → ℝ}
    (hf : ∀ i, MemLp (f i) 4 μ) (hC : ∀ i, 0 ≤ C i)
    (hb : ∀ i, (∫ x, |f i x| ^ 4 ∂μ) ≤ C i) :
    (∫ x, |∏ i, f i x| ∂μ) ≤ ∏ i, C i ^ (1 / 4 : ℝ) := by
  have hle : (k : ℝ≥0∞) ≤ 4 := by exact_mod_cast hk4
  apply (product_lpNorm_bound hk (fun i => (hf i).mono_exponent hle)).trans
  apply Finset.prod_le_prod₀ (fun _ _ => lpNorm_nonneg)
  intro i _
  apply le_trans _ (fourth_lpNorm_le (hf i) (hb i))
  exact ENNReal.toReal_mono (hf i).eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le hle)

private lemma ordered_prod (a b : Fin k → ℝ) (d : ℝ) (i : Fin k) :
    (∏ j, if j < i then a j else if i < j then b j else d) =
      d * (∏ j with j < i, a j) * ∏ j with i < j, b j := by
  have he (j : Fin k) :
      (if j < i then a j else if i < j then b j else d) =
        (if j = i then d else 1) * (if j < i then a j else 1) *
          (if i < j then b j else 1) := by
    rcases lt_trichotomy j i with h | h | h <;> simp [h, ne_of_lt, ne_of_gt, not_lt_of_gt]
  simp_rw [he, Finset.prod_mul_distrib]
  simp [Finset.prod_ite]

private def orderedFactor (f g : Fin k → α → ℝ) (i j : Fin k) : α → ℝ :=
  if j < i then f j else if i < j then g j else fun x => f i x - g i x

private lemma orderedFactor_memLp {p : ℝ≥0∞} {f g : Fin k → α → ℝ}
    (hf : ∀ i, MemLp (f i) p μ) (hg : ∀ i, MemLp (g i) p μ) (i j : Fin k) :
    MemLp (orderedFactor f g i j) p μ := by
  unfold orderedFactor
  split_ifs <;> first | apply hf | apply hg | exact (hf i).sub (hg i)

omit [MeasurableSpace α] in
private lemma product_sub_eq (f g : Fin k → α → ℝ) (x : α) :
    (∏ i, f i x) - ∏ i, g i x = ∑ i, ∏ j, orderedFactor f g i j x := by
  have h := Finset.prod_sub_ordered Finset.univ (fun i => g i x)
    (fun i => g i x - f i x)
  simp only [sub_sub_cancel] at h
  have he : ∀ i, (∏ j, orderedFactor f g i j x) =
      (f i x - g i x) * (∏ j with j < i, f j x) * ∏ j with i < j, g j x := by
    intro i
    simpa only [orderedFactor, ite_apply] using
      ordered_prod (fun j => f j x) (fun j => g j x) (f i x - g i x) i
  simp_rw [he]
  have hn : (∑ i, (g i x - f i x) * (∏ j with j < i, f j x) *
      ∏ j with i < j, g j x) =
      -(∑ i, (f i x - g i x) * (∏ j with j < i, f j x) *
      ∏ j with i < j, g j x) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hn] at h
  linarith

private lemma product_difference_integral_le_sum (hk : 0 < k)
    {f g : Fin k → α → ℝ}
    (hf : ∀ i, MemLp (f i) (k : ℝ≥0∞) μ)
    (hg : ∀ i, MemLp (g i) (k : ℝ≥0∞) μ) :
    (∫ x, |(∏ i, f i x) - ∏ i, g i x| ∂μ) ≤
      ∑ i, ∫ x, |∏ j, orderedFactor f g i j x| ∂μ := by
  have hi (i : Fin k) := product_integrable hk (orderedFactor_memLp hf hg i)
  calc
    _ ≤ ∫ x, ∑ i, |∏ j, orderedFactor f g i j x| ∂μ := by
      apply integral_mono ((product_integrable hk hf).sub (product_integrable hk hg)).abs
        (integrable_finsetSum _ (fun i _ => (hi i).abs))
      intro x
      change |(∏ i, f i x) - ∏ i, g i x| ≤ _
      rw [product_sub_eq]
      exact Finset.abs_sum_le_sum_abs _ _
    _ = _ := integral_finsetSum _ (fun i _ => (hi i).abs)

/-- Uniform fourth moments and fourth moment errors bound the replacement of at most four factors. -/
theorem product_fourth_difference_bound [IsProbabilityMeasure μ]
    (hk : 0 < k) (hk4 : k ≤ 4) {f g : Fin k → α → ℝ} {K D : ℝ}
    (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hf : ∀ i, MemLp (f i) 4 μ ∧ MemLp (g i) 4 μ)
    (hfb : ∀ i, (∫ x, |f i x| ^ 4 ∂μ) ≤ K)
    (hgb : ∀ i, (∫ x, |g i x| ^ 4 ∂μ) ≤ K)
    (hdb : ∀ i, (∫ x, |f i x - g i x| ^ 4 ∂μ) ≤ D) :
    (∫ x, |(∏ i, f i x) - ∏ i, g i x| ∂μ) ≤
      (k : ℝ) * D ^ (1 / 4 : ℝ) * K ^ (((k : ℝ) - 1) / 4) := by
  have hm (i j : Fin k) := orderedFactor_memLp (fun i => (hf i).1) (fun i => (hf i).2) i j
  have hb (i : Fin k) :
      (∫ x, |∏ j, orderedFactor f g i j x| ∂μ) ≤
        D ^ (1 / 4 : ℝ) * K ^ (((k : ℝ) - 1) / 4) := by
    have h := product_fourth_bound hk hk4 (hm i)
      (C := fun j => if j = i then D else K)
      (fun j => by split_ifs <;> assumption) (fun j => by
        by_cases hji : j = i
        · subst j; simpa [orderedFactor] using hdb i
        · unfold orderedFactor
          split_ifs with hlt hgt
          · simpa [hji] using hfb j
          · simpa [hji] using hgb j
          · exact (hji (le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt))).elim)
    apply h.trans_eq
    calc
      _ = D ^ (1 / 4 : ℝ) * (K ^ (1 / 4 : ℝ)) ^ (k - 1) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
        simp only [ite_true]
        congr 1
        calc
          _ = ∏ _j ∈ Finset.univ.erase i, K ^ (1 / 4 : ℝ) := by
            apply Finset.prod_congr rfl
            intro j hj
            simp [(Finset.mem_erase.mp hj).1]
          _ = _ := by simp
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hK]
        congr 2
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hk.ne')]
        ring
  calc
    _ ≤ ∑ i, ∫ x, |∏ j, orderedFactor f g i j x| ∂μ :=
      product_difference_integral_le_sum hk
        (fun i => (hf i).1.mono_exponent (by exact_mod_cast hk4))
        (fun i => (hf i).2.mono_exponent (by exact_mod_cast hk4))
    _ ≤ ∑ _i : Fin k, D ^ (1 / 4 : ℝ) * K ^ (((k : ℝ) - 1) / 4) :=
      Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by simp; ring

end
end D5.S3.Arith.Robin.ForwardKernel.FiniteProductMomentBounds
