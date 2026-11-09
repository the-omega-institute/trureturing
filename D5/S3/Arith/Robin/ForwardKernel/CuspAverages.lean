/- GID: D5/S3/Arith/Robin/ForwardKernel/CuspAverages
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/CuspAverages
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pointwise estimates and length comparison for averaged clipped logarithmic cusps. -/

import D5.S3.Arith.Robin.ForwardKernel.ClippedLogEnergy
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Pointwise cusp analysis and concavity comparison of averaging lengths. -/

namespace D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpness

open Set MeasureTheory
open scoped Topology
noncomputable section

private lemma clip_pos {h k : ℝ} (hh : 0 < h) (hhk : h < k) (x : ℝ) :
    0 < min k (max h |x|) :=
  lt_min (hh.trans hhk) (hh.trans_le (le_max_left _ _))

private lemma jump_continuous {h k : ℝ} (hh : 0 < h) (hhk : h < k) (q y : ℝ) :
    Continuous (fun s => clippedLog h k (y + s * q) - clippedLog h k y) := by
  exact ((clippedLog_continuous hh hhk).comp
    (continuous_const.add (continuous_id.mul_const q))).sub continuous_const

lemma jump_integrable {h k : ℝ} (hh : 0 < h) (hhk : h < k)
    (q y a b : ℝ) :
    IntervalIntegrable (fun s => clippedLog h k (y + s * q) - clippedLog h k y)
      volume a b :=
  (jump_continuous hh hhk q y).intervalIntegrable a b

lemma clip_mono {h k x z : ℝ} (hh : 0 < h) (hhk : h < k)
    (hx : 0 ≤ x) (hxz : x ≤ z) : clippedLog h k x ≤ clippedLog h k z := by
  apply Real.log_le_log (div_pos (clip_pos hh hhk _) (hh.trans hhk))
  apply div_le_div_of_nonneg_right _ (hh.trans hhk).le
  simp only [abs_of_nonneg hx, abs_of_nonneg (hx.trans hxz)]
  exact min_le_min_left _ (max_le_max_left _ hxz)

lemma clip_range {h k : ℝ} (hh : 0 < h) (hhk : h < k) (x : ℝ) :
    Real.log (h / k) ≤ clippedLog h k x ∧ clippedLog h k x ≤ 0 := by
  constructor
  · apply Real.log_le_log (div_pos hh (hh.trans hhk))
    exact div_le_div_of_nonneg_right (le_min hhk.le (le_max_left _ _)) (hh.trans hhk).le
  · apply Real.log_nonpos (div_nonneg (clip_pos hh hhk _).le (hh.trans hhk).le)
    exact (div_le_one (hh.trans hhk)).2 (min_le_left _ _)

private lemma clip_on {h k x : ℝ} (hh : 0 < h) (hhk : h < k) (hx : h ≤ x) :
    clippedLog h k x = min (Real.log k) (Real.log x) - Real.log k := by
  rw [clippedLog_log_space hh hhk (hh.trans_le hx).ne',
    abs_of_pos (hh.trans_le hx),
    max_eq_right (Real.log_le_log hh hx)]

/-- On the nonnegative axis every forward cusp average lies between zero and its depth.
Consumed by the cross-energy estimate and moving-length transport. -/
theorem cuspAverage_bounds {h k q y : ℝ}
    (hh : 0 < h) (hhk : h < k) (hq : 0 ≤ q) (hy : 0 ≤ y) :
    0 ≤ cuspAverage h k q y ∧ cuspAverage h k q y ≤ Real.log (k / h) := by
  have hk := hh.trans hhk
  constructor
  · apply intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
    intro s hs
    exact sub_nonneg.mpr (clip_mono hh hhk hy (by nlinarith [hs.1]))
  · calc
      _ ≤ ∫ _s in (0 : ℝ)..1, Real.log (k / h) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (jump_integrable hh hhk q y 0 1) (intervalIntegrable_const)
        intro s _
        have hb := clip_range hh hhk y
        have ht := (clip_range hh hhk (y + s * q)).2
        rw [Real.log_div hk.ne' hh.ne']
        rw [Real.log_div hh.ne' hk.ne'] at hb
        linarith
      _ = _ := by simp

/-- The lower clipped interval has an absolute bound for lengths at most twice the inner radius.
Consumed by moving-length transport and the cross-energy estimate. -/
theorem cuspAverage_short_bound {h k q y : ℝ}
    (hh : 0 < h) (hhk : h < k) (hq : 0 ≤ q) (hq₂ : q ≤ 2 * h)
    (hy : y ∈ Icc (0 : ℝ) h) : cuspAverage h k q y ≤ Real.log 3 := by
  have hk := hh.trans hhk
  have he : clippedLog h k y = Real.log (h / k) := by
    simp [clippedLog, abs_of_nonneg hy.1, max_eq_left hy.2, min_eq_right hhk.le]
  calc
    _ ≤ ∫ _s in (0 : ℝ)..1, Real.log 3 := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (jump_integrable hh hhk q y 0 1) intervalIntegrable_const
      intro s hs
      rw [he, clippedLog, Real.log_div (clip_pos hh hhk _).ne' hk.ne',
        Real.log_div hh.ne' hk.ne']
      have ht : min k (max h |y + s * q|) ≤ 3 * h := by
        apply (min_le_right _ _).trans
        rw [abs_of_nonneg (by positivity [hy.1, hs.1])]
        exact max_le (by linarith) (by nlinarith [hy.2, mul_le_mul_of_nonneg_right hs.2 hq])
      have hl := Real.log_le_log (clip_pos hh hhk (y + s * q)) ht
      rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hh.ne'] at hl
      linarith
    _ = _ := by simp

private lemma clip_concave {h k : ℝ} (hh : 0 < h) (hhk : h < k) :
    ConcaveOn ℝ (Ici h) (clippedLog h k) := by
  have hc := ((concaveOn_const (Real.log k) (convex_Ioi (0 : ℝ))).inf
    strictConcaveOn_log_Ioi.concaveOn).add_const (-Real.log k)
  exact (hc.subset (fun x hx => hh.trans_le hx) (convex_Ici h)).congr
    (fun x hx => (clip_on hh hhk hx).symm)

/-- Increasing the length increases the average by at most the length ratio above the inner radius.
Consumed by moving-length transport. -/
theorem cuspAverage_length_comparison {h k r q y : ℝ}
    (hh : 0 < h) (hhk : h < k) (hr : 0 < r) (hrq : r ≤ q) (hy : h ≤ y) :
    cuspAverage h k r y ≤ cuspAverage h k q y ∧
      cuspAverage h k q y ≤ (q / r) * cuspAverage h k r y := by
  have hq : 0 < q := hr.trans_le hrq
  have hy0 : 0 ≤ y := hh.le.trans hy
  constructor
  · apply intervalIntegral.integral_mono_on (by norm_num)
      (jump_integrable hh hhk r y 0 1) (jump_integrable hh hhk q y 0 1)
    intro s hs
    exact sub_le_sub_right (clip_mono hh hhk (by positivity [hs.1])
      (by nlinarith [hs.1])) _
  · simp only [cuspAverage]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by norm_num)
      (jump_integrable hh hhk q y 0 1)
      ((jump_integrable hh hhk r y 0 1).const_mul (q / r))
    intro s hs
    have hc := (clip_concave hh hhk).2 hy
      (show y + s * q ∈ Ici h by change h ≤ y + s * q; nlinarith [hs.1])
      (show 0 ≤ 1 - r / q by rw [sub_nonneg, div_le_one hq]; exact hrq)
      (div_nonneg hr.le hq.le) (by ring : 1 - r / q + r / q = 1)
    have he : (1 - r / q) • y + (r / q) • (y + s * q) = y + s * r := by
      simp only [smul_eq_mul]
      field_simp
      ring
    rw [he] at hc
    simp only [smul_eq_mul] at hc
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hr).2
    have hc' := mul_le_mul_of_nonneg_left hc hq.le
    field_simp at hc' ⊢
    nlinarith

/-- The cusp average is continuous in its base point.
Consumed by the cross-energy integrability arguments. -/
theorem cuspAverage_continuous {h k : ℝ} (hh : 0 < h) (hhk : h < k) (q : ℝ) :
    Continuous (cuspAverage h k q) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact ((clippedLog_continuous hh hhk).comp
    (continuous_fst.add (continuous_snd.mul_const q))).sub
      ((clippedLog_continuous hh hhk).comp continuous_fst)

private lemma increment_le_ratio {h k y t : ℝ} (hh : 0 < h) (hhk : h < k)
    (hy : h ≤ y) (ht : 0 ≤ t) :
    clippedLog h k (y + t) - clippedLog h k y ≤ t / y := by
  have hy0 := hh.trans_le hy
  by_cases hyk : k ≤ y
  · rw [clippedLog_eq_zero (hh.trans hhk) (by rw [abs_of_nonneg (by positivity)]; linarith),
      clippedLog_eq_zero (hh.trans hhk) (by simpa [abs_of_pos hy0] using hyk)]
    simpa only [sub_self] using div_nonneg ht hy0.le
  · have hyk := (not_le.mp hyk).le
    rw [clip_on hh hhk (by linarith), clip_on hh hhk hy,
      min_eq_right (Real.log_le_log hy0 hyk)]
    have hl := Real.log_le_sub_one_of_pos (div_pos (by positivity : 0 < y + t) hy0)
    rw [Real.log_div (by positivity : y + t ≠ 0) hy0.ne'] at hl
    have hm := min_le_right (Real.log k) (Real.log (y + t))
    have he : (y + t) / y - 1 = t / y := by field_simp; ring
    rw [he] at hl
    linarith

/-- Above the inner radius the cusp average is at most half the length-to-base ratio.
Consumed by the upper endpoint estimate for cross energy. -/
theorem cuspAverage_le_half_ratio {h k q y : ℝ} (hh : 0 < h) (hhk : h < k)
    (hq : 0 ≤ q) (hy : h ≤ y) : cuspAverage h k q y ≤ q / (2 * y) := by
  calc
    _ ≤ ∫ s in (0 : ℝ)..1, s * q / y := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (jump_integrable hh hhk q y 0 1) (by apply Continuous.intervalIntegrable; fun_prop)
      intro s hs
      exact increment_le_ratio hh hhk hy (mul_nonneg hs.1 hq)
    _ = _ := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_mul_const, integral_id]
      ring

/-- A one-sided quadratic error bound for the short cusp average, including the inner endpoint.
Consumed by the cross-energy estimate. -/
theorem cuspAverage_inner_approx {h k y : ℝ} (hh : 0 < h) (h₂ : 2 * h ≤ k)
    (hyh : h ≤ y) (hyk : y ≤ k - h) :
    |cuspAverage h k h y - h / (2 * y)| ≤ h ^ 2 / y ^ 2 := by
  have hhk : h < k := by linarith
  have hy0 := hh.trans_le hyh
  have he (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      clippedLog h k (y + s * h) - clippedLog h k y = Real.log (1 + s * h / y) := by
    have hys : h ≤ y + s * h := by nlinarith [hs.1]
    have hys' : y + s * h ≤ k := by nlinarith [hs.2]
    rw [clip_on hh hhk hys, clip_on hh hhk hyh,
      min_eq_right (Real.log_le_log (hh.trans_le hys) hys'),
      min_eq_right (Real.log_le_log hy0 (by linarith))]
    have hr : 1 + s * h / y = (y + s * h) / y := by field_simp
    rw [hr, Real.log_div (hh.trans_le hys).ne' hy0.ne']; ring
  rw [abs_le]
  constructor
  · have hl : h / (2 * y) - h ^ 2 / y ^ 2 ≤ cuspAverage h k h y := by
      calc
        _ = ∫ s in (0 : ℝ)..1, s * h / y - h ^ 2 / y ^ 2 := by
          rw [intervalIntegral.integral_sub
            (by apply Continuous.intervalIntegrable; fun_prop) intervalIntegrable_const,
            intervalIntegral.integral_div, intervalIntegral.integral_mul_const, integral_id]
          simp; ring
        _ ≤ _ := by
          apply intervalIntegral.integral_mono_on (by norm_num)
            (by apply Continuous.intervalIntegrable; fun_prop)
            (jump_integrable hh hhk h y 0 1)
          intro s hs
          rw [he s hs]
          have ht : 0 ≤ s * h / y := by positivity [hs.1]
          have ht1 : s * h / y ≤ h / y := div_le_div_of_nonneg_right
            (by nlinarith [hs.2]) hy0.le
          have hl := Real.le_log_one_add_of_nonneg ht
          have hsq : (s * h / y) ^ 2 ≤ h ^ 2 / y ^ 2 := by
            simpa [div_pow] using pow_le_pow_left₀ ht ht1 2
          have hd : 0 < s * h / y + 2 := by positivity
          have hrat : s * h / y - (s * h / y) ^ 2 ≤ 2 * (s * h / y) / (s * h / y + 2) := by
            apply (le_div_iff₀ hd).2
            nlinarith [sq_nonneg (s * h / y), mul_nonneg ht (sq_nonneg (s * h / y))]
          linarith
    linarith
  · have hu := cuspAverage_le_half_ratio hh hhk hh.le hyh
    have hn : 0 ≤ h ^ 2 / y ^ 2 := by positivity
    linarith

/-- Above the inner radius the remaining logarithmic depth bounds every forward average.
Consumed by the cross-energy estimate and moving-length transport. -/
theorem cuspAverage_le_log_ratio {h k q y : ℝ} (hh : 0 < h) (hhk : h < k)
    (hyh : h ≤ y) (hyk : y ≤ k) : cuspAverage h k q y ≤ Real.log (k / y) := by
  have hy0 := hh.trans_le hyh
  calc
    _ ≤ ∫ _s in (0 : ℝ)..1, Real.log (k / y) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (jump_integrable hh hhk q y 0 1) intervalIntegrable_const
      intro s _
      rw [clip_on hh hhk hyh, min_eq_right (Real.log_le_log hy0 hyk),
        Real.log_div (hh.trans hhk).ne' hy0.ne']
      linarith [(clip_range hh hhk (y + s * q)).2]
    _ = _ := by simp

/-- The outer-length cusp average has an elementary closed logarithmic form.
Consumed by the exact outer integral and the cross-energy estimate. -/
theorem cuspAverage_outer_eq {h k y : ℝ} (hh : 0 < h) (hhk : h < k)
    (hyh : h ≤ y) (hyk : y ≤ k) :
    cuspAverage h k k y = Real.log (k / y) - 1 +
      (y / k) * (1 + Real.log (k / y)) := by
  have hk := hh.trans hhk
  have hy0 := hh.trans_le hyh
  have hi (a b : ℝ) : IntervalIntegrable (clippedLog h k) volume a b := by
    exact (clippedLog_continuous hh hhk).intervalIntegrable a b
  have hmain : (∫ t in y..k, clippedLog h k t) =
      k * Real.log k - y * Real.log y - k + y - (k - y) * Real.log k := by
    calc
      _ = ∫ t in y..k, Real.log t - Real.log k := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hyk] at ht
        rw [clip_on hh hhk (hyh.trans ht.1), min_eq_right
          (Real.log_le_log (hy0.trans_le ht.1) ht.2)]
      _ = _ := by
        rw [intervalIntegral.integral_sub (intervalIntegral.intervalIntegrable_log')
          intervalIntegrable_const, integral_log, intervalIntegral.integral_const]
        simp [smul_eq_mul]
  have htail : (∫ t in k..(k + y), clippedLog h k t) = 0 := by
    calc
      _ = ∫ _t in k..(k + y), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by linarith : k ≤ k + y)] at ht
        exact clippedLog_eq_zero hk (by rw [abs_of_nonneg (hk.le.trans ht.1)]; exact ht.1)
      _ = 0 := by simp
  have hs := intervalIntegral.mul_integral_comp_mul_add (f := clippedLog h k) (a := 0) (b := 1) k y
  simp only [mul_zero, zero_add, mul_one] at hs
  have ha : (∫ s in (0 : ℝ)..1, clippedLog h k (y + s * k)) =
      ∫ s in (0 : ℝ)..1, clippedLog h k (k * s + y) := by
    congr 1; funext s; congr 1; ring
  have hj : cuspAverage h k k y =
      (∫ s in (0 : ℝ)..1, clippedLog h k (y + s * k)) - clippedLog h k y := by
    rw [cuspAverage, intervalIntegral.integral_sub (by
      exact ((clippedLog_continuous hh hhk).comp
        (continuous_const.add (continuous_id.mul_const k))).intervalIntegrable 0 1)
      intervalIntegrable_const]
    simp
  have htotal := intervalIntegral.integral_add_adjacent_intervals (hi y k) (hi k (k + y))
  rw [htail, hmain, add_zero] at htotal
  rw [hj, ha, clip_on hh hhk hyh, min_eq_right (Real.log_le_log hy0 hyk),
    Real.log_div hk.ne' hy0.ne']
  have hval : k * (∫ s in (0 : ℝ)..1, clippedLog h k (k * s + y)) =
      k * Real.log k - y * Real.log y - k + y - (k - y) * Real.log k := hs.trans htotal.symm
  apply (mul_left_cancel₀ hk.ne')
  field_simp
  nlinarith [hval]

end
end D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpness
