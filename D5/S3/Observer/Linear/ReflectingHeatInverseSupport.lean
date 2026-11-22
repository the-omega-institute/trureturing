/- GID: D5/S3/Observer/Linear/ReflectingHeatInverseSupport
   generality: I
   mirror-B: D5/B/S3/Observer/Linear/ReflectingHeatInverseSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recover supported inverse Fourier densities and their reflecting heat moments. -/

import D5.S3.Fourier.InverseFourierSupport
import D5.S3.Observer.Linear.ReflectingHeatDirectionalBound
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Inverse Fourier support and moments for the actual reflecting heat interpolant. -/

namespace D5.S3.Observer.Linear.ReflectingHeatInterpolation

open Complex Filter MeasureTheory Set Topology
open scoped FourierTransform ENNReal
open D5.S3.Fourier.InverseFourierSupport
open D5.S3.Weil.ZetaGamma.FormCore.LineFourier
open D5.S3.Observer.Linear.ReflectingHeatStripBound

noncomputable section

private theorem differentiable_fourierLaplace_of_support {v : ℝ → ℂ} {a : ℝ}
    (ha : 0 ≤ a) (hv : Integrable v) (hsupp : ∀ t : ℝ, a < |t| → v t = 0) :
    Differentiable ℂ (fun z => ∫ t : ℝ, exp (-I * z * (t : ℂ)) * v t) := by
  intro z₀
  let f : ℂ → ℝ → ℂ := fun z t => exp (-I * z * (t : ℂ)) * v t
  let f' : ℂ → ℝ → ℂ := fun z t => exp (-I * z * (t : ℂ)) * (-I * (t : ℂ)) * v t
  have exp_bound (z : ℂ) (t : ℝ) (ht : ‖t‖ ≤ a) :
      ‖exp (-I * z * (t : ℂ))‖ ≤ Real.exp (‖z‖ * a) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ ‖-I * z * (t : ℂ)‖ := Complex.re_le_norm _
      _ = ‖z‖ * ‖t‖ := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_left ht (norm_nonneg _)
  have fmeas (z : ℂ) : AEStronglyMeasurable (f z) volume :=
    (by fun_prop : Continuous fun t : ℝ => exp (-I * z * (t : ℂ))).aestronglyMeasurable.mul
      hv.aestronglyMeasurable
  have hf : Integrable (f z₀) := by
    apply (hv.norm.const_mul (Real.exp (‖z₀‖ * a))).mono' (fmeas z₀)
    filter_upwards [] with t
    by_cases ht : ‖t‖ ≤ a
    · rw [show ‖f z₀ t‖ = ‖exp (-I * z₀ * (t : ℂ))‖ * ‖v t‖ by simp [f]]
      exact mul_le_mul_of_nonneg_right (exp_bound z₀ t ht) (norm_nonneg _)
    · have hz := hsupp t (by simpa only [Real.norm_eq_abs] using lt_of_not_ge ht)
      simp [f, hz]
  have hf'meas : AEStronglyMeasurable (f' z₀) volume := by
    have h : Continuous (fun t : ℝ => exp (-I * z₀ * (t : ℂ)) * (-I * (t : ℂ))) := by
      fun_prop
    exact h.aestronglyMeasurable.mul hv.aestronglyMeasurable
  let bound : ℝ → ℝ := fun t => (Real.exp ((‖z₀‖ + 1) * a) * a) * ‖v t‖
  have hbound : ∀ᵐ t : ℝ, ∀ z ∈ Metric.ball z₀ 1, ‖f' z t‖ ≤ bound t := by
    filter_upwards [] with t
    intro z hz
    by_cases ht : ‖t‖ ≤ a
    · have hzn : ‖z‖ ≤ ‖z₀‖ + 1 := by
        have hd : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hz
        have h := norm_add_le (z - z₀) z₀
        rw [sub_add_cancel] at h
        linarith
      have he := (exp_bound z t ht).trans
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hzn ha))
      simp only [f', bound, norm_mul, norm_neg, norm_I, Complex.norm_real, one_mul]
      gcongr
    · have hzero := hsupp t (by simpa only [Real.norm_eq_abs] using lt_of_not_ge ht)
      simp [f', bound, hzero]
  have hderiv : ∀ᵐ t : ℝ, ∀ z ∈ Metric.ball z₀ 1,
      HasDerivAt (fun w => f w t) (f' z t) z := by
    filter_upwards [] with t
    intro z _
    have hinner : HasDerivAt (fun w : ℂ => -I * w * (t : ℂ)) (-I * (t : ℂ)) z := by
      simpa using (((hasDerivAt_const z (-I)).mul (hasDerivAt_id z)).mul_const (t : ℂ))
    simpa [f, f', mul_assoc] using (hinner.cexp).mul_const (v t)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := f) (F' := f') (bound := bound) (Metric.ball_mem_nhds z₀ zero_lt_one)
    (Eventually.of_forall fmeas) hf hf'meas hbound (hv.norm.const_mul _) hderiv).2.differentiableAt

private theorem eq_fourierLaplace_of_inverse {F : ℂ → ℂ} {a : ℝ} {v : ℝ → ℂ}
    (hF : Differentiable ℂ F) (ha : 0 ≤ a) (hv : Integrable v) (hv₂ : MemLp v 2 volume)
    (hsupp : ∀ t : ℝ, a < |t| → v t = 0)
    (hg : MemLp (frequencyRestriction F) 2 volume)
    (hinv : hv₂.toLp v = (Lp.fourierTransformₗᵢ ℝ ℂ).symm (hg.toLp (frequencyRestriction F))) :
    ∀ z : ℂ, (∫ t : ℝ, exp (-I * z * (t : ℂ)) * v t) = F z := by
  let W : ℂ → ℂ := fun z => ∫ t : ℝ, exp (-I * z * (t : ℂ)) * v t
  have hW : Differentiable ℂ W := differentiable_fourierLaplace_of_support ha hv hsupp
  have heq : 𝓕 (hv₂.toLp v) = hg.toLp (frequencyRestriction F) := by
    change (Lp.fourierTransformₗᵢ ℝ ℂ) (hv₂.toLp v) = _
    rw [hinv, LinearIsometryEquiv.apply_symm_apply]
  have hae : (𝓕 v : ℝ → ℂ) =ᵐ[volume] frequencyRestriction F := by
    have hh := raw_fourier_ae_eq_L2 hv hv₂
    rw [heq] at hh
    exact hh.trans hg.coeFn_toLp
  have hfg := Measure.eq_of_ae_eq hae (continuous_raw_fourier hv)
    (hF.continuous.comp (by fun_prop : Continuous fun ξ : ℝ => (((2 * Real.pi) * ξ : ℝ) : ℂ)))
  have hreal (x : ℝ) : W (x : ℂ) = F (x : ℂ) := by
    have hx : 2 * Real.pi * (x / (2 * Real.pi)) = x :=
      mul_div_cancel₀ _ (show 2 * Real.pi ≠ 0 by positivity)
    have hgx := congrFun hfg (x / (2 * Real.pi))
    rw [frequencyRestriction, hx] at hgx
    rw [← hgx, Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [Algebra.smul_def]
    congr 2
    have hp : -2 * Real.pi * t * (x / (2 * Real.pi)) = -x * t := by
      linear_combination -t * hx
    rw [hp, ofReal_mul, ofReal_neg]
    ring
  have hfrequent : ∃ᶠ z in 𝓝[≠] (0 : ℂ), W z = F z := by
    let seq : ℕ → ℂ := fun n => (((n : ℝ) + 1)⁻¹ : ℝ)
    have hseq : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have hn : Tendsto seq atTop (𝓝[≠] (0 : ℂ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, Eventually.of_forall fun n => ?_⟩
      · simpa [seq, Function.comp_def] using continuous_ofReal.continuousAt.tendsto.comp hseq
      · have hpos : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
        change ((↑(((n : ℝ) + 1)⁻¹) : ℂ) ∉ ({0} : Set ℂ))
        exact fun h => hpos.ne' (Complex.ofReal_eq_zero.mp (mem_singleton_iff.mp h))
    exact hn.frequently (Frequently.of_forall fun _ => hreal _)
  exact congrFun ((Complex.analyticOnNhd_univ_iff_differentiable.mpr hW).eq_of_frequently_eq
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hF) hfrequent)

/-- The canonical inverse Fourier class of the reflecting heat interpolant has an integrable
representative supported on the centered interval of length `L`. Its exponential moments
evaluate the interpolant at the actual reflecting mode rates. -/
theorem momentInterpolant_inverse_support (n : ℕ) (j : Mode n) (M : ℂ → ℂ)
    (hM_entire : Differentiable ℂ M) {L A B C : ℝ} {m : ℕ} (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hM_radial : ∀ z : ℂ, ‖M z‖ ≤ C * (1 + ‖z‖) ^ m * Real.exp (L / 2 * ‖z‖))
    (hM_real : ∀ ω : ℝ, ∃ ζ : ℂ, ζ ≠ 0 ∧
      ζ + ζ⁻¹ = (ω : ℂ) * I - 2 ∧ 1 ≤ ‖ζ‖ ∧
      ‖M (ω : ℂ)‖ ≤ A * (1 + B * |ω|) / ‖ζ‖ ^ n) :
    let g := frequencyRestriction (momentInterpolant n j M)
    ∃ hg : MemLp g 2 volume,
      ∃ v : ℝ → ℂ, Integrable v ∧
        (v =ᵐ[volume] (Lp.fourierTransformₗᵢ ℝ ℂ).symm (hg.toLp g)) ∧
        (∀ t : ℝ, L / 2 < |t| → v t = 0) ∧
        (∀ z : ℂ, (∫ t : ℝ, exp (-I * z * (t : ℂ)) * v t) = momentInterpolant n j M z) ∧
        (∀ k : Mode n, (∫ t : ℝ, exp (-(rate n k : ℂ) * (t : ℂ)) * v t) =
          if k = j then (nodalDerivative n j : ℂ) * M (-(rate n j : ℂ) * I) else 0) := by
  obtain ⟨hF, h₂, _, hbound, hnodes⟩ :=
    momentInterpolant_contour_bounds n j M hM_entire hL hA hM_radial hM_real
  obtain ⟨hg, hsupp⟩ := inverse_fourier_L2_support hF h₂ hbound
  let u := (Lp.fourierTransformₗᵢ ℝ ℂ).symm
    (hg.toLp (frequencyRestriction (momentInterpolant n j M)))
  let s := Icc (-(L / 2)) (L / 2)
  let v := s.indicator (u : ℝ → ℂ)
  have hv₂ : MemLp v 2 volume := (Lp.memLp u).indicator measurableSet_Icc.nullMeasurableSet
  have hvzero (t : ℝ) (ht : t ∉ s) : v t = 0 := indicator_of_notMem ht _
  have hae : v =ᵐ[volume] u := by
    filter_upwards [hsupp] with t ht
    by_cases h : t ∈ s
    · exact indicator_of_mem h _
    · rw [hvzero t h, ht (lt_of_not_ge (fun he => h (abs_le.mp he)))]
  have hv : Integrable v :=
    memLp_one_iff_integrable.mp
      (hv₂.mono_exponent_of_measure_support_ne_top hvzero isCompact_Icc.measure_lt_top.ne
        (by norm_num))
  have hvabs (t : ℝ) (ht : L / 2 < |t|) : v t = 0 :=
    hvzero t (fun h => (not_le_of_gt ht) (abs_le.mpr h))
  have hvclass : hv₂.toLp v = u :=
    Lp.ext (hv₂.coeFn_toLp.trans hae)
  have hrecover := eq_fourierLaplace_of_inverse hF (by positivity) hv hv₂ hvabs hg hvclass
  refine ⟨hg, v, hv, hae, hvabs, hrecover, fun k => ?_⟩
  have he : -I * (-(rate n k : ℂ) * I) = -(rate n k : ℂ) := by
    calc
      _ = (rate n k : ℂ) * (I * I) := by ring
      _ = _ := by rw [I_mul_I, mul_neg_one]
  simpa only [he, hnodes] using hrecover (-(rate n k : ℂ) * I)

#print axioms momentInterpolant_inverse_support

end
end D5.S3.Observer.Linear.ReflectingHeatInterpolation
