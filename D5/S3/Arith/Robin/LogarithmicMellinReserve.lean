/- GID: D5/S3/Arith/Robin/LogarithmicMellinReserve
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/LogarithmicMellinReserve
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Two logarithmic envelopes pay the full absolute Mellin mass. -/

import D5.S3.Arith.Robin.MellinWeightedVariation
import D5.S3.Weil.ZetaPntBounds.ZetaBoundsUpper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Topology
open MeasureTheory Set Filter

namespace D5.S3.Arith.Robin.LogarithmicMellinReserve

private noncomputable def lowPrimitive (b y : ℝ) : ℝ :=
  y ^ b / b ^ 2 - Real.log y * y ^ b / b

noncomputable def highPrimitive (a y : ℝ) : ℝ :=
  -(Real.log y * y ^ (-a)) / a - y ^ (-a) / a ^ 2

private lemma hasDerivAt_lowPrimitive {b y : ℝ} (hb : 0 < b) (hy : 0 < y) :
    HasDerivAt (lowPrimitive b) (-Real.log y * y ^ (b - 1)) y := by
  have hp := Real.hasDerivAt_rpow_const (p := b) (Or.inl hy.ne')
  have hdp : HasDerivAt (lowPrimitive b)
      (b * y ^ (b - 1) / b ^ 2 -
        (y⁻¹ * y ^ b + Real.log y * (b * y ^ (b - 1))) / b) y := by
    simpa only [lowPrimitive, Pi.sub_apply, Pi.div_apply, Pi.mul_apply] using!
      (hp.div_const (b ^ 2)).sub
        (((Real.hasDerivAt_log hy.ne').mul hp).div_const b)
  convert hdp using 1
  have heq : y ^ b = y ^ (b - 1) * y := by
    calc
      y ^ b = y ^ ((b - 1) + 1) := by congr 1; ring
      _ = y ^ (b - 1) * y := by rw [Real.rpow_add hy, Real.rpow_one]
  rw [heq]
  field_simp [hb.ne', hy.ne']
  <;> ring

private lemma lowPrimitive_zero {b : ℝ} (hb : 0 < b) : lowPrimitive b 0 = 0 := by
  simp [lowPrimitive, Real.zero_rpow hb.ne']

private lemma continuousOn_lowPrimitive {b : ℝ} (hb : 0 < b) :
    ContinuousOn (lowPrimitive b) (Icc 0 1) := by
  intro y hy
  by_cases hy0 : y = 0
  · subst y
    have hp : Tendsto (fun y : ℝ => y ^ b) (𝓝[>] 0) (nhds 0) := by
      have hc : ContinuousAt (fun y : ℝ => y ^ b) 0 :=
        (Real.continuous_rpow_const hb.le).continuousAt
      simpa [Real.zero_rpow hb.ne'] using
        (hc.tendsto.mono_left inf_le_left :
          Tendsto (fun y : ℝ => y ^ b) (𝓝[>] 0) (nhds ((0 : ℝ) ^ b)))
    have hlog := tendsto_log_mul_rpow_nhdsGT_zero hb
    have hlim : Tendsto (lowPrimitive b) (𝓝[>] 0) (nhds 0) := by
      simpa [lowPrimitive] using! (hp.div_const (b ^ 2)).sub (hlog.div_const b)
    apply (continuousWithinAt_Ioi_iff_Ici.mp
      (show ContinuousWithinAt (lowPrimitive b) (Ioi 0) 0 from by
        simpa [ContinuousWithinAt, lowPrimitive_zero hb] using hlim)).mono
    exact Icc_subset_Ici_self
  · exact (hasDerivAt_lowPrimitive hb (lt_of_le_of_ne hy.1 (Ne.symm hy0))).continuousAt.continuousWithinAt

private lemma low_log_integrable {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun y : ℝ => -Real.log y * y ^ (b - 1)) (Ioc 0 1) := by
  apply intervalIntegral.integrableOn_deriv_of_nonneg (continuousOn_lowPrimitive hb)
    (fun y hy => hasDerivAt_lowPrimitive hb hy.1)
  intro y hy
  exact mul_nonneg (neg_nonneg.mpr (Real.log_nonpos hy.1.le hy.2.le))
    (Real.rpow_nonneg hy.1.le _)

private lemma integral_low_log {b : ℝ} (hb : 0 < b) :
    (∫ y in Ioc (0 : ℝ) 1, -Real.log y * y ^ (b - 1)) = 1 / b ^ 2 := by
  have hint := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    (low_log_integrable hb)
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (by norm_num : (0 : ℝ) ≤ 1) (continuousOn_lowPrimitive hb)
      (fun y hy => hasDerivAt_lowPrimitive hb hy.1) hint,
    lowPrimitive_zero hb]
  simp [lowPrimitive]

lemma hasDerivAt_highPrimitive {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    HasDerivAt (highPrimitive a) (Real.log y * y ^ (-a - 1)) y := by
  have hp := Real.hasDerivAt_rpow_const (p := -a) (Or.inl hy.ne')
  have hdp : HasDerivAt (highPrimitive a)
      (-(y⁻¹ * y ^ (-a) + Real.log y * (-a * y ^ (-a - 1))) / a -
        (-a * y ^ (-a - 1)) / a ^ 2) y := by
    simpa only [highPrimitive, Pi.sub_apply, Pi.div_apply, Pi.mul_apply, Pi.neg_apply] using!
      ((((Real.hasDerivAt_log hy.ne').mul hp).neg).div_const a).sub (hp.div_const (a ^ 2))
  convert hdp using 1
  have heq : y ^ (-a) = y ^ (-a - 1) * y := by
    calc
      y ^ (-a) = y ^ ((-a - 1) + 1) := by congr 1; ring
      _ = y ^ (-a - 1) * y := by rw [Real.rpow_add hy, Real.rpow_one]
  rw [heq]
  field_simp [ha.ne', hy.ne']
  <;> ring

lemma tendsto_highPrimitive {a : ℝ} (ha : 0 < a) :
    Tendsto (highPrimitive a) atTop (nhds 0) := by
  have hlog : Tendsto (fun y : ℝ => Real.log y * y ^ (-a)) atTop (nhds 0) := by
    apply ((isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [Real.rpow_neg hy.le, div_eq_mul_inv]
  have hp := tendsto_rpow_neg_atTop ha
  simpa [highPrimitive] using! (hlog.neg.div_const a).sub (hp.div_const (a ^ 2))

private lemma high_log_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => Real.log y * y ^ (-a - 1)) (Ioi 1) := by
  have h : IntegrableOn (fun y : ℝ => ‖y ^ (-a - 1)‖ * ‖Real.log y‖)
      (Ioi (1 : ℝ)) := by
    simpa only [Nat.cast_one] using
      (integrable_log_over_pow (r := -a) (by linarith) (N := 1) (by decide))
  have heq : (fun y : ℝ => ‖y ^ (-a - 1)‖ * ‖Real.log y‖) =ᵐ[
      volume.restrict (Ioi (1 : ℝ))] (fun y : ℝ => Real.log y * y ^ (-a - 1)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
    have hlog : 0 ≤ Real.log y := Real.log_nonneg hy.le
    have hp : 0 ≤ y ^ (-a - 1) := Real.rpow_nonneg (zero_le_one.trans hy.le) _
    simp only [Real.norm_eq_abs, abs_of_nonneg hp, abs_of_nonneg hlog, mul_comm]
  exact h.congr heq

private lemma integral_high_log {a : ℝ} (ha : 0 < a) :
    (∫ y in Ioi (1 : ℝ), Real.log y * y ^ (-a - 1)) = 1 / a ^ 2 := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun y hy => hasDerivAt_highPrimitive ha (zero_lt_one.trans_le hy))
    (fun y hy => mul_nonneg (Real.log_nonneg hy.le)
      (Real.rpow_nonneg (zero_le_one.trans hy.le) _))
    (tendsto_highPrimitive ha)]
  simp [highPrimitive]

noncomputable def reserve (d a μ α : ℝ) : ℝ :=
  d / (1 - α) + a / (1 - α) ^ 2 + μ * (1 / α + 1 / α ^ 2)

private lemma low_weighted_bound (ρ : ℝ → ℝ) (d a : ℝ) {α y : ℝ}
    (hy : 0 < y) (hlow : |ρ y| ≤ d * y + a * (-Real.log y * y)) :
    |ρ y| * y ^ (-α - 1) ≤ d * y ^ (-α) + a * (-Real.log y * y ^ (-α)) := by
  have h := mul_le_mul_of_nonneg_right (hlow)
    (Real.rpow_nonneg hy.le (-α - 1))
  have heq : y * y ^ (-α - 1) = y ^ (-α) := by
    calc
      y * y ^ (-α - 1) = y ^ (1 : ℝ) * y ^ (-α - 1) := by rw [Real.rpow_one]
      _ = y ^ ((1 : ℝ) + (-α - 1)) := (Real.rpow_add hy _ _).symm
      _ = y ^ (-α) := by congr 1; ring
  calc
    _ ≤ (d * y + a * (-Real.log y * y)) * y ^ (-α - 1) := h
    _ = d * (y * y ^ (-α - 1)) + a * (-Real.log y * (y * y ^ (-α - 1))) := by ring
    _ = _ := by rw [heq]

private lemma high_weighted_bound (ρ : ℝ → ℝ) (μ : ℝ) {α y : ℝ}
    (hy : 1 ≤ y) (hhigh : |ρ y| ≤ μ * (1 + Real.log y)) :
    |ρ y| * y ^ (-α - 1) ≤ μ * (y ^ (-α - 1) + Real.log y * y ^ (-α - 1)) := by
  have h := mul_le_mul_of_nonneg_right (hhigh)
    (Real.rpow_nonneg (show 0 ≤ y by linarith) (-α - 1))
  calc
    _ ≤ (μ * (1 + Real.log y)) * y ^ (-α - 1) := h
    _ = _ := by ring

private lemma low_rpow_integrable {α : ℝ} (hα1 : α < 1) :
    IntegrableOn (fun y : ℝ => y ^ (-α)) (Ioc 0 1) := by
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -α))

private lemma integral_low_rpow {α : ℝ} (hα1 : α < 1) :
    (∫ y in Ioc (0 : ℝ) 1, y ^ (-α)) = 1 / (1 - α) := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have h := integral_rpow
    (a := (0 : ℝ)) (b := 1) (Or.inl (show -1 < -α by linarith))
  simpa only [show -α + 1 = 1 - α by ring, Real.one_rpow,
    Real.zero_rpow (sub_pos.mpr hα1).ne', sub_zero] using h

private lemma integral_high_rpow {α : ℝ} (hα : 0 < α) :
    (∫ y in Ioi (1 : ℝ), y ^ (-α - 1)) = 1 / α := by
  rw [integral_Ioi_rpow_of_lt (show -α - 1 < -1 by linarith) zero_lt_one]
  simp

/-- Two logarithmic envelopes pay the absolute Mellin mass on the whole positive axis. -/
theorem logarithmic_mellin_reserve (ρ : ℝ → ℝ) (d a μ : ℝ) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hρ : Measurable ρ)
    (hlow : ∀ y : ℝ, 0 < y → y ≤ 1 → |ρ y| ≤ d * y + a * (-Real.log y * y))
    (hhigh : ∀ y : ℝ, 1 ≤ y → |ρ y| ≤ μ * (1 + Real.log y)) :
    IntegrableOn (fun y => |ρ y| * y ^ (-α - 1)) (Ioi 0) ∧
      (∫ y in Ioi (0 : ℝ), |ρ y| * y ^ (-α - 1)) ≤ reserve d a μ α := by
  have hb : 0 < 1 - α := sub_pos.mpr hα1
  have hpowLow := low_rpow_integrable hα1
  have hlogLow : IntegrableOn (fun y : ℝ => -Real.log y * y ^ (-α)) (Ioc 0 1) := by
    simpa only [show (1 - α) - 1 = -α by ring] using low_log_integrable hb
  have hpowHigh := integrableOn_Ioi_rpow_of_lt (show -α - 1 < -1 by linarith) zero_lt_one
  have hlogHigh := high_log_integrable hα
  have hmajorLow := (hpowLow.const_mul d).add (hlogLow.const_mul a)
  have hmajorHigh := (hpowHigh.add hlogHigh).const_mul μ
  have hmeas : Measurable (fun y : ℝ => |ρ y| * y ^ (-α - 1)) := by
    have hRabs : Measurable (fun y : ℝ => |ρ y|) := by
      simpa only [Real.norm_eq_abs] using hρ.norm
    apply hRabs.mul
    fun_prop
  have hl : IntegrableOn (fun y => |ρ y| * y ^ (-α - 1)) (Ioc 0 1) := by
    apply Integrable.mono' hmajorLow hmeas.aestronglyMeasurable
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hy.1.le _))]
    exact low_weighted_bound ρ d a hy.1 (hlow y hy.1 hy.2)
  have hh : IntegrableOn (fun y => |ρ y| * y ^ (-α - 1)) (Ioi 1) := by
    apply Integrable.mono' hmajorHigh hmeas.aestronglyMeasurable
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (zero_le_one.trans hy.le) _))]
    exact high_weighted_bound ρ μ hy.le (hhigh y hy.le)
  have hfull : IntegrableOn (fun y => |ρ y| * y ^ (-α - 1)) (Ioi 0) := by
    simpa only [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] using hl.union hh
  have hlowBound : (∫ y in Ioc (0 : ℝ) 1, |ρ y| * y ^ (-α - 1)) ≤
      d / (1 - α) + a / (1 - α) ^ 2 := by
    calc
      _ ≤ ∫ y in Ioc (0 : ℝ) 1,
          d * y ^ (-α) + a * (-Real.log y * y ^ (-α)) := by
        apply setIntegral_mono_on hl hmajorLow measurableSet_Ioc
        intro y hy
        exact low_weighted_bound ρ d a hy.1 (hlow y hy.1 hy.2)
      _ = _ := by
        rw [integral_add (hpowLow.const_mul _) (hlogLow.const_mul _),
          integral_const_mul, integral_const_mul, integral_low_rpow hα1]
        have hlogEq : (∫ y in Ioc (0 : ℝ) 1, -Real.log y * y ^ (-α)) = 1 / (1 - α) ^ 2 := by
          simpa only [show (1 - α) - 1 = -α by ring] using integral_low_log hb
        rw [hlogEq]
        ring
  have hhighBound : (∫ y in Ioi (1 : ℝ), |ρ y| * y ^ (-α - 1)) ≤
      μ * (1 / α + 1 / α ^ 2) := by
    calc
      _ ≤ ∫ y in Ioi (1 : ℝ),
          μ * (y ^ (-α - 1) + Real.log y * y ^ (-α - 1)) := by
        apply setIntegral_mono_on hh hmajorHigh measurableSet_Ioi
        intro y hy
        exact high_weighted_bound ρ μ hy.le (hhigh y hy.le)
      _ = _ := by
        rw [integral_const_mul, integral_add hpowHigh hlogHigh,
          integral_high_rpow hα, integral_high_log hα]
  refine ⟨hfull, ?_⟩
  have hsplit := intervalIntegral.integral_interval_add_Ioi hfull hh
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hsplit
  unfold reserve
  linarith


/-- The two envelopes also pay every weighted adjacent clipped Robin integral difference. -/
theorem logarithmic_weighted_variation (ρ : ℝ → ℝ) (d a μ x α : ℝ)
    (hx : 1 < x) (hα : 0 < α) (hα1 : α < 1) (hρ : Measurable ρ)
    (hlow : ∀ y : ℝ, 0 < y → y ≤ 1 → |ρ y| ≤ d * y + a * (-Real.log y * y))
    (hhigh : ∀ y : ℝ, 1 ≤ y → |ρ y| ≤ μ * (1 + Real.log y)) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ α *
      |MellinWeightedVariation.genericP ρ x (j + 1) -
        MellinWeightedVariation.genericP ρ x (j + 2)|) ∧
    (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ α *
      |MellinWeightedVariation.genericP ρ x (j + 1) -
        MellinWeightedVariation.genericP ρ x (j + 2)|) ≤
      MellinWeightedVariation.variationConstant x α * reserve d a μ α := by
  obtain ⟨hM, hpay⟩ := logarithmic_mellin_reserve ρ d a μ hα hα1 hρ hlow hhigh
  have hv := MellinWeightedVariation.mellin_weighted_variation ρ hx hα hα1 hρ hM
  have hC : 0 ≤ MellinWeightedVariation.variationConstant x α := by
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hl : 0 < Real.log x := Real.log_pos hx
    have hb : 0 < 1 - α := sub_pos.mpr hα1
    unfold MellinWeightedVariation.variationConstant
    positivity
  exact ⟨hv.1, hv.2.trans (mul_le_mul_of_nonneg_left hpay hC)⟩

end D5.S3.Arith.Robin.LogarithmicMellinReserve
