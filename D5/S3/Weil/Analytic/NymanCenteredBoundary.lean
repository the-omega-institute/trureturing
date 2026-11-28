/- GID: D5/S3/Weil/Analytic/NymanCenteredBoundary
   generality: I
   mirror-B: none(waiver:nyman-centered-prime-analysis)
   mirror-E: none(waiver:nyman-centered-prime-analysis)
   anchors: []
   utility: none
   digest: Absolute integrability and right continuity at the centered prime Mellin endpoint. -/

import D5.S3.Weil.Analytic.NymanCenteredReciprocal
import D5.S3.Weil.Analytic.NymanCenteredMomentTail
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Absolute convergence at the boundary of the centered prime Mellin transform. -/

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace NymanCenteredBoundary

open NymanPrimeDilations NymanCenteredReciprocal NymanCenteredMomentTail

private theorem continuous_centeredPrimeDilations : Continuous centeredPrimeDilations := by
  have hc := continuousOn_centeredPrimeDilations_inv.comp
    (continuousOn_inv₀.mono (fun t (ht : t ∈ Ioi (0 : ℝ)) => ne_of_gt ht))
    (fun t (ht : t ∈ Ioi (0 : ℝ)) => mem_Ioi.mpr (inv_pos.mpr (mem_Ioi.mp ht)))
  have hpos : ContinuousOn centeredPrimeDilations (Ioi 0) := by
    simpa only [Function.comp_def, inv_inv] using hc
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : 0 < x
  · exact hpos.continuousAt (Ioi_mem_nhds hx)
  · have hzero : centeredPrimeDilations =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds (show x < 1 by linarith)] with t ht
      exact centeredPrimeDilations_eq_zero_of_le_one ht.le
    exact continuousAt_const.congr_of_eventuallyEq hzero

theorem integrable_centeredPrime_weighted :
    IntegrableOn (fun x : ℝ => centeredPrimeDilations x / x ^ 2) (Ioi 0) := by
  have hc : Continuous (fun x : ℝ => centeredPrimeDilations x / x ^ 2) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x = 0
    · subst x
      have hzero : (fun t : ℝ => centeredPrimeDilations t / t ^ 2) =ᶠ[𝓝 0]
          fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with t ht
        rw [centeredPrimeDilations_eq_zero_of_le_one ht.le, zero_div]
      exact continuousAt_const.congr_of_eventuallyEq hzero
    · exact continuous_centeredPrimeDilations.continuousAt.div
        (continuous_id.pow 2).continuousAt (pow_ne_zero _ hx)
  obtain ⟨T, _, htail⟩ := integrable_centeredPrime_weighted_tail hc.measurable
  have hcompact : IntegrableOn (fun x : ℝ => centeredPrimeDilations x / x ^ 2)
      (Icc 0 T) := hc.continuousOn.integrableOn_Icc
  apply (hcompact.union htail).mono_set
  intro x hx
  by_cases h : x ≤ T
  · exact Or.inl ⟨hx.le, h⟩
  · exact Or.inr (lt_of_not_ge h)

private def transformIntegrand (σ x : ℝ) : ℂ :=
  (x : ℂ) ^ (-(σ : ℂ) - 1) * (centeredPrimeDilations x : ℂ)

theorem tendsto_mellin_neg_from_right :
    Tendsto (fun σ : ℝ => mellin (fun x => (centeredPrimeDilations x : ℂ)) (-(σ : ℂ)))
      (𝓝[>] (1 : ℝ)) (𝓝 (mellin (fun x => (centeredPrimeDilations x : ℂ)) (-1))) := by
  have h := integrable_centeredPrime_weighted.norm
  have habs : Integrable (fun x : ℝ => |centeredPrimeDilations x / x ^ 2|)
      (volume.restrict (Ioi 0)) := by simpa only [Real.norm_eq_abs] using h
  have hlim : Tendsto (fun σ : ℝ => ∫ x in Ioi (0 : ℝ), transformIntegrand σ x)
      (𝓝[>] (1 : ℝ)) (𝓝 (∫ x in Ioi (0 : ℝ), transformIntegrand 1 x)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x : ℝ =>
      |centeredPrimeDilations x / x ^ 2|) _ _ habs
    · apply (ae_restrict_iff' measurableSet_Ioi).mpr
      apply Eventually.of_forall
      intro x hx
      have he : Continuous (fun σ : ℝ => -(σ : ℂ) - 1) :=
        Complex.continuous_ofReal.neg.sub continuous_const
      exact (((continuous_const_cpow' (by exact_mod_cast ne_of_gt hx)).comp he).mul
        continuous_const).continuousAt.continuousWithinAt
    · apply Eventually.of_forall
      intro σ
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      unfold transformIntegrand
      apply ContinuousOn.mul
      · exact fun x hx => (Complex.continuousAt_ofReal_cpow_const x _
          (Or.inr (ne_of_gt hx))).continuousWithinAt
      · exact (Complex.continuous_ofReal.comp continuous_centeredPrimeDilations).continuousOn
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      apply (ae_restrict_iff' measurableSet_Ioi).mpr
      apply Eventually.of_forall
      intro x hx
      by_cases h₁ : x ≤ 1
      · simp [transformIntegrand, centeredPrimeDilations_eq_zero_of_le_one h₁]
      · have hx₁ : 1 ≤ x := le_of_not_ge h₁
        have hsq : 0 < x ^ 2 := pow_pos (mem_Ioi.mp hx) 2
        rw [transformIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_cpow_eq_rpow_re_of_pos hx, abs_div, abs_of_pos hsq]
        simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.one_re]
        have hpow : x ^ (-σ - 1) ≤ (x ^ 2)⁻¹ := by
          calc
            _ ≤ x ^ (-(2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hx₁ (by
              have := mem_Ioi.mp hσ
              linarith)
            _ = _ := by rw [Real.rpow_neg hx.le, Real.rpow_ofNat]
        simpa only [div_eq_mul_inv, mul_comm (|centeredPrimeDilations x|)] using
          mul_le_mul_of_nonneg_right hpow (abs_nonneg (centeredPrimeDilations x))
  simpa [mellin, transformIntegrand, smul_eq_mul] using hlim

end NymanCenteredBoundary
