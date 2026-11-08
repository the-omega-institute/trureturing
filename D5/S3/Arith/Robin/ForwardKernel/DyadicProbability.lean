/- GID: D5/S3/Arith/Robin/ForwardKernel/DyadicProbability
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/DyadicProbability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logarithmic density on a dyadic interval gives a probability measure and moment conversions. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The logarithmic probability measure on a dyadic interval. -/

namespace D5.S3.Arith.Robin.ForwardKernel.DyadicProbability

open Set MeasureTheory

noncomputable section
set_option autoImplicit false

def dyadicProbabilityMeasure (X : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc X (2 * X))).withDensity
    (fun x => ENNReal.ofReal (1 / (x * Real.log 2)))

private lemma density_measurable :
    Measurable (fun x : ℝ => ENNReal.ofReal (1 / (x * Real.log 2))) := by
  fun_prop

private lemma density_nonneg {X : ℝ} (hX : 0 < X) :
    ∀ᵐ x ∂volume.restrict (Ioc X (2 * X)), 0 ≤ 1 / (x * Real.log 2) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact one_div_nonneg.mpr (mul_nonneg (hX.trans hx.1).le (Real.log_pos (by norm_num)).le)

/-- Integration against the dyadic probability measure is normalized logarithmic integration. -/
theorem dyadicProbabilityMeasure_integral {X : ℝ} (hX : 0 < X) (f : ℝ → ℝ) :
    (∫ x, f x ∂dyadicProbabilityMeasure X) =
      (∫ x in X..(2 * X), f x / x) / Real.log 2 := by
  rw [dyadicProbabilityMeasure,
    integral_withDensity_eq_integral_toReal_smul density_measurable
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  rw [intervalIntegral.integral_of_le (by linarith : X ≤ 2 * X), ← integral_div]
  apply integral_congr_ae
  filter_upwards [density_nonneg hX] with x hx
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul]
  ring

/-- Logarithmically integrable functions are integrable for the dyadic probability measure. -/
theorem dyadicProbabilityMeasure_integrable {X : ℝ} {f : ℝ → ℝ} (hX : 0 < X)
    (hf : IntervalIntegrable (fun x => f x / x) volume X (2 * X)) :
    Integrable f (dyadicProbabilityMeasure X) := by
  apply (integrable_withDensity_iff_integrable_smul' density_measurable
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).2
  have hi := ((intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by linarith : X ≤ 2 * X)).mp hf).div_const (Real.log 2)
  apply hi.congr
  filter_upwards [density_nonneg hX] with x hx
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul]
  ring

/-- The normalized logarithmic density has total mass one on each positive dyadic interval. -/
theorem dyadicProbabilityMeasure_univ {X : ℝ} (hX : 0 < X) :
    dyadicProbabilityMeasure X univ = 1 := by
  have hi : IntervalIntegrable (fun x : ℝ => 1 / (x * Real.log 2)) volume X (2 * X) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div
      (continuousOn_id.mul continuousOn_const)
    intro x hx
    rw [uIcc_of_le (by linarith : X ≤ 2 * X)] at hx
    exact mul_ne_zero (ne_of_gt (hX.trans_le hx.1)) (ne_of_gt (Real.log_pos (by norm_num)))
  have he : (∫ x in X..(2 * X), 1 / (x * Real.log 2)) = 1 := by
    simp_rw [div_mul_eq_div_div]
    rw [intervalIntegral.integral_div, integral_one_div_of_pos hX
      (by linarith), mul_div_cancel_right₀ 2 hX.ne', div_self (ne_of_gt (Real.log_pos (by norm_num)))]
  rw [dyadicProbabilityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : X ≤ 2 * X)).mp hi)
      (density_nonneg hX),
    ← intervalIntegral.integral_of_le (by linarith : X ≤ 2 * X), he]
  simp

/-- The dyadic logarithmic measure is a probability measure when its left endpoint is positive. -/
theorem dyadicProbabilityMeasure_isProbabilityMeasure {X : ℝ} (hX : 0 < X) :
    IsProbabilityMeasure (dyadicProbabilityMeasure X) :=
  ⟨dyadicProbabilityMeasure_univ hX⟩

end
end D5.S3.Arith.Robin.ForwardKernel.DyadicProbability
