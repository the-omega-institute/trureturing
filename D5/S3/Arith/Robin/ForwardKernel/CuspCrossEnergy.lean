/- GID: D5/S3/Arith/Robin/ForwardKernel/CuspCrossEnergy
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/CuspCrossEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The cusp cross energy has an absolute logarithmic error bound. -/

import D5.S3.Arith.Robin.ForwardKernel.CuspAverages

/-! Exact integration and an absolute error estimate for the cusp cross energy. -/

namespace D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpness

open Set MeasureTheory
open scoped Topology
noncomputable section

/-- The logarithmically weighted outer average has an exact primitive.
Consumed by the cross-energy estimate. -/
theorem cuspAverage_outer_integral {h k : ℝ} (hh : 0 < h) (hhk : h < k) :
    (∫ y in h..k, cuspAverage h k k y / y) =
      (Real.log (k / h)) ^ 2 / 2 - Real.log (k / h) + 2 -
        (Real.log (k / h) + 2) * (h / k) := by
  have hk := hh.trans hhk
  let F : ℝ → ℝ := fun y => -(Real.log k - Real.log y) ^ 2 / 2 +
    (Real.log k - Real.log y) + (y / k) * (2 + (Real.log k - Real.log y))
  have hd (y : ℝ) (hy : y ∈ uIcc h k) :
      HasDerivAt F (cuspAverage h k k y / y) y := by
    rw [uIcc_of_le hhk.le] at hy
    have hy0 := hh.trans_le hy.1
    have hv : HasDerivAt (fun t => Real.log k - Real.log t) (-1 / y) y := by
      convert (hasDerivAt_const y (Real.log k)).sub
        (Real.hasDerivAt_log hy0.ne') using 1 <;> simp [neg_div, one_div]
    have hd := (((hv.pow 2).neg.div_const 2).add hv).add
      (((hasDerivAt_id y).div_const k).mul ((hasDerivAt_const y 2).add hv))
    rw [cuspAverage_outer_eq hh hhk hy.1 hy.2, Real.log_div hk.ne' hy0.ne']
    convert hd using 1
    · ext t
      simp only [F, Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.pow_apply, id_eq] <;> ring
    · dsimp
      field_simp
      ring
  have hi : IntervalIntegrable (fun y => cuspAverage h k k y / y) volume h k := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hhk.le]
    exact (cuspAverage_continuous hh hhk k).continuousOn.div continuousOn_id
      (fun y hy => (hh.trans_le hy.1).ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  dsimp [F]
  rw [Real.log_div hk.ne' hh.ne']
  field_simp
  ring

private lemma product_integrable {h k : ℝ} (hh : 0 < h) (hhk : h < k) (a b : ℝ) :
    IntervalIntegrable (fun y => cuspAverage h k h y * cuspAverage h k k y) volume a b :=
  ((cuspAverage_continuous hh hhk h).mul (cuspAverage_continuous hh hhk k)).intervalIntegrable a b

private lemma proxy_integrable {h k a b : ℝ} (hh : 0 < h) (hhk : h < k)
    (ha : h ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun y => h / (2 * y) * cuspAverage h k k y) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply ContinuousOn.mul _ (cuspAverage_continuous hh hhk k).continuousOn
  apply continuousOn_const.div (continuousOn_const.mul continuousOn_id)
  intro y hy
  exact mul_ne_zero (by norm_num) (hh.trans_le (ha.trans hy.1)).ne'

private lemma proxy_sub_nonneg {h k y : ℝ} (hh : 0 < h) (hhk : h < k)
    (hy : h ≤ y) :
    0 ≤ h / (2 * y) * cuspAverage h k k y -
      cuspAverage h k h y * cuspAverage h k k y := by
  exact sub_nonneg.mpr (mul_le_mul_of_nonneg_right
    (cuspAverage_le_half_ratio hh hhk hh.le hy)
    (cuspAverage_bounds hh hhk (hh.trans hhk).le (hh.le.trans hy)).1)

private lemma lower_integral_bound {h k : ℝ} (hh : 0 < h) (hhk : h < k) :
    0 ≤ (∫ y in (0 : ℝ)..h, cuspAverage h k h y * cuspAverage h k k y) ∧
    (∫ y in (0 : ℝ)..h, cuspAverage h k h y * cuspAverage h k k y) ≤
      2 * h * Real.log (k / h) := by
  have hL : 0 ≤ Real.log (k / h) := Real.log_nonneg ((one_le_div hh).2 hhk.le)
  constructor
  · apply intervalIntegral.integral_nonneg hh.le
    intro y hy
    exact mul_nonneg (cuspAverage_bounds hh hhk hh.le hy.1).1
      (cuspAverage_bounds hh hhk (hh.trans hhk).le hy.1).1
  · calc
      _ ≤ ∫ _y in (0 : ℝ)..h, 2 * Real.log (k / h) := by
        apply intervalIntegral.integral_mono_on hh.le (product_integrable hh hhk 0 h)
          intervalIntegrable_const
        intro y hy
        have hs := cuspAverage_short_bound hh hhk hh.le (by linarith) hy
        have hl : Real.log (3 : ℝ) ≤ 2 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
          norm_num at this ⊢; exact this
        exact mul_le_mul (hs.trans hl) (cuspAverage_bounds hh hhk (hh.trans hhk).le hy.1).2
          (cuspAverage_bounds hh hhk (hh.trans hhk).le hy.1).1 (by norm_num)
      _ = _ := by simp <;> ring

private lemma middle_error_bound {h k : ℝ} (hh : 0 < h) (h₂ : 2 * h ≤ k) :
    (∫ y in h..(k - h),
      (h / (2 * y) * cuspAverage h k k y -
        cuspAverage h k h y * cuspAverage h k k y)) ≤ h * Real.log (k / h) := by
  have hhk : h < k := by linarith
  have hm : h ≤ k - h := by linarith
  have hL : 0 ≤ Real.log (k / h) := Real.log_nonneg ((one_le_div hh).2 hhk.le)
  have hi : IntervalIntegrable (fun y : ℝ => h ^ 2 * Real.log (k / h) / y ^ 2)
      volume h (k - h) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hm]
    exact continuousOn_const.div (continuousOn_id.pow 2)
      (fun y hy => pow_ne_zero _ (hh.trans_le hy.1).ne')
  calc
    _ ≤ ∫ y in h..(k - h), h ^ 2 * Real.log (k / h) / y ^ 2 := by
      apply intervalIntegral.integral_mono_on hm
        ((proxy_integrable hh hhk le_rfl hm).sub (product_integrable hh hhk h (k - h))) hi
      intro y hy
      have hB := (cuspAverage_bounds hh hhk (hh.trans hhk).le (hh.le.trans hy.1))
      have hD := (abs_le.mp (cuspAverage_inner_approx hh h₂ hy.1 hy.2)).1
      have hdepth : cuspAverage h k k y ≤ Real.log (k / h) := hB.2
      calc
        _ = (h / (2 * y) - cuspAverage h k h y) * cuspAverage h k k y := by ring
        _ ≤ (h ^ 2 / y ^ 2) * Real.log (k / h) :=
          mul_le_mul (by linarith) hdepth hB.1 (by positivity)
        _ = _ := by ring
    _ = h ^ 2 * Real.log (k / h) * (1 / h - 1 / (k - h)) := by
      simp_rw [div_eq_mul_inv]
      rw [intervalIntegral.integral_const_mul]
      have he : (∫ y in h..(k - h), (y ^ 2)⁻¹) = 1 / h - 1 / (k - h) := by
        have hz := integral_zpow (a := h) (b := k - h) (n := -2)
          (Or.inr ⟨by norm_num, notMem_uIcc_of_lt hh (hh.trans_le hm)⟩)
        norm_num at hz
        rw [hz]
        ring
      rw [he]
      simp only [one_div, one_mul]
    _ ≤ _ := by
      have hn : 0 ≤ 1 / (k - h) := by positivity
      have he : h ^ 2 * Real.log (k / h) * (1 / h) = h * Real.log (k / h) := by field_simp <;> ring
      nlinarith [mul_nonneg (show 0 ≤ h ^ 2 * Real.log (k / h) by positivity) hn]

private lemma upper_endpoint_bounds {h k y : ℝ} (hh : 0 < h) (h₂ : 2 * h ≤ k)
    (hy : y ∈ Icc (k - h) k) :
    cuspAverage h k h y ≤ h / k ∧ cuspAverage h k k y ≤ 2 * h / k := by
  have hhk : h < k := by linarith
  have hk := hh.trans hhk
  have hyh : h ≤ y := by linarith [hy.1]
  have hy0 := hh.trans_le hyh
  constructor
  · exact (cuspAverage_le_half_ratio hh hhk hh.le hyh).trans
      (div_le_div_of_nonneg_left hh.le hk (by linarith [hy.1]))
  · apply (cuspAverage_le_log_ratio hh hhk hyh hy.2).trans
    have hl := Real.log_le_sub_one_of_pos (div_pos hk hy0)
    apply hl.trans
    have he : k / y - 1 = (k - y) / y := by field_simp <;> ring
    rw [he]
    apply (div_le_div_iff₀ hy0 hk).2
    calc
      (k - y) * k ≤ h * k := mul_le_mul_of_nonneg_right (by linarith [hy.1]) hk.le
      _ ≤ (2 * h) * y := by
        have hky : k ≤ 2 * y := by linarith [hy.1]
        nlinarith [mul_le_mul_of_nonneg_left hky hh.le]

private lemma tail_error_bound {h k : ℝ} (hh : 0 < h) (h₂ : 2 * h ≤ k) :
    (∫ y in (k - h)..k,
      (h / (2 * y) * cuspAverage h k k y -
        cuspAverage h k h y * cuspAverage h k k y)) ≤ h * Real.log (k / h) := by
  have hhk : h < k := by linarith
  have hm : h ≤ k - h := by linarith
  have hmk : k - h ≤ k := by linarith
  calc
    _ ≤ ∫ _y in (k - h)..k, Real.log (k / h) := by
      apply intervalIntegral.integral_mono_on hmk
        ((proxy_integrable hh hhk hm hmk).sub (product_integrable hh hhk (k - h) k))
        intervalIntegrable_const
      intro y hy
      have hyh := hm.trans hy.1
      have hy0 := hh.trans_le hyh
      have hB := cuspAverage_bounds hh hhk (hh.trans hhk).le hy0.le
      have hA := cuspAverage_bounds hh hhk hh.le hy0.le
      have hep := upper_endpoint_bounds hh h₂ hy
      have hratio : h / (2 * y) ≤ h / k :=
        div_le_div_of_nonneg_left hh.le (hh.trans hhk) (by linarith [hy.1])
      have hprod : h / (2 * y) * cuspAverage h k k y ≤ (h / k) * (2 * h / k) :=
        mul_le_mul hratio hep.2 hB.1 (div_nonneg hh.le (hh.trans hhk).le)
      have hhalf : h / k ≤ (1 / 2 : ℝ) := by
        apply (div_le_iff₀ (hh.trans hhk)).2; linarith
      have hlog := Real.one_sub_inv_le_log_of_pos (div_pos (hh.trans hhk) hh)
      simp only [inv_div] at hlog
      have hpow := pow_le_pow_left₀ (div_nonneg hh.le (hh.trans hhk).le) hhalf 2
      nlinarith [mul_nonneg hA.1 hB.1]
    _ = _ := by simp <;> ring

private lemma energy_proxy_bound {h k : ℝ} (hh : 0 < h) (h₂ : 2 * h ≤ k) :
    |cuspCrossEnergy h k -
      h / 2 * (∫ y in h..k, cuspAverage h k k y / y)| ≤
        4 * h * Real.log (k / h) := by
  have hhk : h < k := by linarith
  have hm : h ≤ k - h := by linarith
  have hmk : k - h ≤ k := by linarith
  let f := fun y => cuspAverage h k h y * cuspAverage h k k y
  let g := fun y => h / (2 * y) * cuspAverage h k k y
  have heq : (∫ y in h..k, g y) = h / 2 * (∫ y in h..k, cuspAverage h k k y / y) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y _
    dsimp [g]; ring
  have hsplit : cuspCrossEnergy h k = (∫ y in (0 : ℝ)..h, f y) + ∫ y in h..k, f y :=
    (intervalIntegral.integral_add_adjacent_intervals
      (product_integrable hh hhk 0 h) (product_integrable hh hhk h k)).symm
  have hd : (∫ y in h..k, g y - f y) = (∫ y in h..k, g y) - ∫ y in h..k, f y :=
    intervalIntegral.integral_sub (proxy_integrable hh hhk le_rfl hhk.le)
      (product_integrable hh hhk h k)
  have hd0 : 0 ≤ ∫ y in h..k, g y - f y := by
    apply intervalIntegral.integral_nonneg hhk.le
    intro y hy
    exact proxy_sub_nonneg hh hhk hy.1
  have hd1 : (∫ y in h..k, g y - f y) ≤ 2 * h * Real.log (k / h) := by
    have hs := intervalIntegral.integral_add_adjacent_intervals
      ((proxy_integrable hh hhk le_rfl hm).sub (product_integrable hh hhk h (k - h)))
      ((proxy_integrable hh hhk hm hmk).sub (product_integrable hh hhk (k - h) k))
    change (∫ y in h..(k - h), g y - f y) + (∫ y in (k - h)..k, g y - f y) = _ at hs
    linarith [middle_error_bound hh h₂, tail_error_bound hh h₂]
  obtain ⟨hf0, hf1⟩ := lower_integral_bound hh hhk
  rw [hsplit, ← heq, abs_le]
  dsimp [f] at *
  constructor <;> linarith

/-- An absolute constant bounds the error in the inner–outer cusp cross energy.
Consumed by moving-length transport and the spike transport theorem. -/
theorem cuspCrossEnergy_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ h k : ℝ, 0 < h → 2 * h ≤ k →
      |cuspCrossEnergy h k - h * (Real.log (k / h)) ^ 2 / 4| ≤
        C * h * Real.log (k / h) := by
  refine ⟨10, by norm_num, ?_⟩
  intro h k hh h₂
  have hhk : h < k := by linarith
  have hk := hh.trans hhk
  let L := Real.log (k / h)
  have hL : 0 ≤ L := Real.log_nonneg ((one_le_div hh).2 hhk.le)
  have ht0 : 0 ≤ h / k := by positivity
  have ht1 : h / k ≤ 1 := (div_le_one hk).2 hhk.le
  have ht2 : h / k ≤ 1 / 2 := by apply (div_le_iff₀ hk).2; linarith
  have hL2 : (1 / 2 : ℝ) ≤ L := by
    have hl := Real.one_sub_inv_le_log_of_pos (div_pos hk hh)
    simp only [inv_div] at hl
    dsimp [L]
    linarith
  have hI : |(∫ y in h..k, cuspAverage h k k y / y) - L ^ 2 / 2| ≤ 10 * L := by
    rw [cuspAverage_outer_integral hh hhk]
    change |L ^ 2 / 2 - L + 2 - (L + 2) * (h / k) - L ^ 2 / 2| ≤ _
    have hp : 0 ≤ (L + 2) * (h / k) := by positivity
    have hp' : (L + 2) * (h / k) ≤ L + 2 := by nlinarith
    rw [abs_le]
    constructor <;> nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hI (show 0 ≤ h / 2 by positivity)
  have hs : |h / 2 * (∫ y in h..k, cuspAverage h k k y / y) - h * L ^ 2 / 4| ≤
      5 * h * L := by
    have heq : h / 2 * (∫ y in h..k, cuspAverage h k k y / y) - h * L ^ 2 / 4 =
        h / 2 * ((∫ y in h..k, cuspAverage h k k y / y) - L ^ 2 / 2) := by ring
    rw [heq, abs_mul, abs_of_nonneg (show 0 ≤ h / 2 by positivity)]
    convert hscaled using 1 <;> ring
  have he := energy_proxy_bound hh h₂
  have ht := abs_sub_le (cuspCrossEnergy h k)
    (h / 2 * (∫ y in h..k, cuspAverage h k k y / y)) (h * L ^ 2 / 4)
  change |cuspCrossEnergy h k - h * L ^ 2 / 4| ≤ 10 * h * L
  nlinarith [mul_nonneg hh.le hL]

end
end D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpness
