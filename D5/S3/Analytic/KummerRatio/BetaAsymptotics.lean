/- GID: D5/S3/Analytic/KummerRatio/BetaAsymptotics
   generality: G
   mirror-B: D5/B/S3/Analytic/KummerRatio/BetaAsymptotics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.PeakFunction, mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.Basic, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics, mathlib/module/Mathlib.Topology.Order.Bornology]
   utility: none
   digest: Gamma density concentration gives beta integral endpoint asymptotics for all positive parameters. -/

import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.Bornology

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace D5.S3.Analytic.KummerRatio.BetaAsymptotics

private def gammaDensity (d x : ℝ) : ℝ :=
  (Ioi (0 : ℝ)).indicator (fun y => Real.exp (-y) * y ^ (d - 1) / Real.Gamma d) x

private def endpointWeight (s x : ℝ) : ℝ :=
  (Ioo (-1 : ℝ) 1).indicator (fun y => (1 - y) ^ (s - 1)) x

private lemma gammaDensity_nonneg {d : ℝ} (hd : 0 < d) (x : ℝ) :
    0 ≤ gammaDensity d x := by
  unfold gammaDensity
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hx]
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hx.le _))
      (Real.Gamma_pos_of_pos hd).le
  · simp [hx]

private lemma gammaDensity_integral {d : ℝ} (hd : 0 < d) :
    ∫ x, gammaDensity d x = 1 := by
  unfold gammaDensity
  rw [integral_indicator measurableSet_Ioi, integral_div, ← Real.Gamma_eq_integral hd,
    div_self (Real.Gamma_pos_of_pos hd).ne']

private lemma gammaDensity_decay (d : ℝ) :
    Tendsto (fun x : ℝ => ‖x‖ ^ Module.finrank ℝ ℝ * gammaDensity d x)
      (Bornology.cobounded ℝ) (𝓝 0) := by
  rw [IsOrderBornology.cobounded_eq]
  apply Filter.Tendsto.sup
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
    simp [gammaDensity, not_lt_of_ge hx.le]
  · have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero d 1 zero_lt_one).div_const
      (Real.Gamma d)
    simp only [zero_div] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp only [Module.finrank_self, pow_one, gammaDensity,
      Real.norm_eq_abs, abs_of_pos hx, one_mul, neg_mul]
    rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
    have hp : x ^ d = x ^ (d - 1) * x := by
      convert Real.rpow_add hx (d - 1) 1 using 1 <;> simp
    rw [hp]
    ring

private lemma endpointWeight_integrable {s : ℝ} (hs : 0 < s) :
    Integrable (endpointWeight s) := by
  unfold endpointWeight
  rw [integrable_indicator_iff measurableSet_Ioo]
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 2) (r := s - 1)
    (by linarith)).comp_sub_left 1
  have h' : IntervalIntegrable (fun y : ℝ => (1 - y) ^ (s - 1)) volume (-1) 1 := by
    convert h.symm using 1 <;> norm_num
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mp h'

private lemma endpointWeight_continuousAt (s : ℝ) :
    ContinuousAt (endpointWeight s) 0 := by
  have h : ContinuousAt (fun y : ℝ => (1 - y) ^ (s - 1)) 0 := by
    apply ContinuousAt.rpow_const
    · fun_prop
    · norm_num
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)] with y hy
  exact indicator_of_mem hy _

private lemma tendsto_gamma_peak {s d : ℝ} (hs : 0 < s) (hd : 0 < d) :
    Tendsto (fun x : ℝ => ∫ y, (x * gammaDensity d (x * y)) * endpointWeight s y)
      atTop (𝓝 1) := by
  have h := tendsto_integral_comp_smul_smul_of_integrable
    (gammaDensity_nonneg hd) (gammaDensity_integral hd) (gammaDensity_decay d)
    (endpointWeight_integrable hs) (endpointWeight_continuousAt s)
  simpa [endpointWeight, smul_eq_mul] using h

private lemma gamma_peak_eq (s d x : ℝ) (hx : 0 < x) :
    (∫ y, (x * gammaDensity d (x * y)) * endpointWeight s y) =
      (x ^ d / Real.Gamma d) *
        ∫ y in (0 : ℝ)..1, Real.exp (-x * y) * y ^ (d - 1) * (1 - y) ^ (s - 1) := by
  have heq : (fun y => (x * gammaDensity d (x * y)) * endpointWeight s y) =
      (Ioo (0 : ℝ) 1).indicator
        (fun y => (x ^ d / Real.Gamma d) *
          (Real.exp (-x * y) * y ^ (d - 1) * (1 - y) ^ (s - 1))) := by
    funext y
    by_cases hy : y ∈ Ioo (0 : ℝ) 1
    · have hxy : x * y ∈ Ioi (0 : ℝ) := mul_pos hx hy.1
      have hy' : y ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
      simp only [gammaDensity, endpointWeight, indicator_of_mem hy,
        indicator_of_mem hxy, indicator_of_mem hy']
      rw [Real.mul_rpow hx.le hy.1.le]
      have hp : x ^ d = x ^ (d - 1) * x := by
        convert Real.rpow_add hx (d - 1) 1 using 1 <;> simp
      rw [hp]
      simp only [neg_mul]
      ring
    · rw [indicator_of_notMem hy]
      by_cases hy' : y ∈ Ioo (-1 : ℝ) 1
      · have hy0 : ¬ 0 < x * y := by
          have : y ≤ 0 := le_of_not_gt (fun h => hy ⟨h, hy'.2⟩)
          exact not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hx.le this)
        simp [gammaDensity, hy0]
      · simp [endpointWeight, hy']
  rw [heq, integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const_mul]

private lemma reflected_beta_integral (s d x : ℝ) :
    (∫ y in (0 : ℝ)..1, Real.exp (-x * y) * y ^ (d - 1) * (1 - y) ^ (s - 1)) =
      Real.exp (-x) *
        ∫ t in (0 : ℝ)..1, Real.exp (x * t) * t ^ (s - 1) * (1 - t) ^ (d - 1) := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun y : ℝ => Real.exp (-x * y) * y ^ (d - 1) * (1 - y) ^ (s - 1))
    (a := (0 : ℝ)) (b := 1) 1
  simp only [sub_self, sub_zero] at h
  rw [← h, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [show -x * (1 - t) = -x + x * t by ring, Real.exp_add]
  have : 1 - (1 - t) = t := by ring
  rw [this]
  ring

/-- A beta weight has a Gamma endpoint limit under exponential concentration. -/
theorem tendsto_beta_laplace {s d : ℝ} (hs : 0 < s) (hd : 0 < d) :
    Tendsto (fun x : ℝ => Real.exp (-x) * x ^ d *
      (∫ t in (0 : ℝ)..1, Real.exp (x * t) * t ^ (s - 1) * (1 - t) ^ (d - 1)))
      atTop (𝓝 (Real.Gamma d)) := by
  have h := (tendsto_gamma_peak hs hd).mul_const (Real.Gamma d)
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [gamma_peak_eq s d x hx, reflected_beta_integral]
  field_simp [(Real.Gamma_pos_of_pos hd).ne']

end D5.S3.Analytic.KummerRatio.BetaAsymptotics
