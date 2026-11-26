/- GID: D5/S3/Analytic/Laplace/ExponentialMultiplierContour
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/ExponentialMultiplierContour
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A rational exponential smoothing multiplier permits a vertical contour shift. -/

import D5.S3.Weil.ZetaExplicit.VerticalLine
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! Vertical contour shifting for exponentially smoothed inversion. -/

namespace D5.S3.Analytic.Laplace.ExponentialMultiplierContour

open Complex Filter MeasureTheory
open scoped Topology

noncomputable section

/-- The integrand for the exponentially smoothed inversion on the target line `σ`. -/
def smoothed (σ c t : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp ((z - σ) * t) * F z * ((c : ℂ) / ((c : ℂ) + z - σ))

private theorem norm_smoothed_le {σ σ₀ c C p : ℝ} (t : ℝ) {F : ℂ → ℂ}
    (hc : 0 < c) (hC : 0 ≤ C)
    (hF : ∀ a ∈ Set.Icc σ σ₀, ∀ y : ℝ, ‖F ((a : ℂ) + y * I)‖ ≤ C * (1 + |y|) ^ (-p))
    {a y : ℝ} (ha : a ∈ Set.Icc σ σ₀) :
    ‖smoothed σ c t F ((a : ℂ) + y * I)‖ ≤
      (Real.exp ((σ₀ - σ) * |t|) * C * (1 + c)) * (1 + |y|) ^ (-(p + 1)) := by
  let d : ℂ := (c : ℂ) + ((a : ℂ) + y * I) - σ
  have hdre : d.re = c + a - σ := by simp [d]
  have hdim : d.im = y := by simp [d]
  have hdc : c ≤ ‖d‖ := by
    have hd := Complex.re_le_norm d
    rw [hdre] at hd
    linarith [ha.1]
  have hdy : |y| ≤ ‖d‖ := by simpa only [hdim] using Complex.abs_im_le_norm d
  have hm : c / ‖d‖ ≤ (1 + c) / (1 + |y|) := by
    apply (div_le_div_iff₀ (hc.trans_le hdc) (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_left hdy hc.le]
  have he : ‖Complex.exp (((a : ℂ) + y * I - σ) * t)‖ ≤
      Real.exp ((σ₀ - σ) * |t|) := by
    rw [Complex.norm_exp, Real.exp_le_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.sub_re, Complex.add_re, Complex.I_re, zero_mul, add_zero]
    calc
      (a - σ) * t ≤ (a - σ) * |t| :=
        mul_le_mul_of_nonneg_left (le_abs_self t) (sub_nonneg.mpr ha.1)
      _ ≤ (σ₀ - σ) * |t| := by gcongr; exact ha.2
  unfold smoothed
  rw [norm_mul, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  change _ * _ * (c / ‖d‖) ≤ _
  calc
    _ ≤ (Real.exp ((σ₀ - σ) * |t|) * (C * (1 + |y|) ^ (-p))) *
        ((1 + c) / (1 + |y|)) := by
      have hprod := mul_le_mul he (hF a ha y) (norm_nonneg _) (Real.exp_nonneg _)
      exact mul_le_mul hprod hm (by positivity) (by positivity)
    _ = (Real.exp ((σ₀ - σ) * |t|) * C * (1 + c)) *
        ((1 + |y|) ^ (-p) * (1 + |y|) ^ (-1 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one]
      ring
    _ = _ := by
      have hy : 0 < 1 + |y| := by positivity
      rw [← Real.rpow_add hy, show -p + (-1) = -(p + 1) by ring]

/-- Polynomial strip decay and the multiplier give integrable vertical sections,
vanishing horizontal edges at both ends, and equality of the full vertical integrals. -/
theorem smoothed_vertical_shift {σ σ₀ c C p : ℝ} (hσσ₀ : σ < σ₀)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 0 < p) (t : ℝ) {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, z.re ∈ Set.Icc σ σ₀ → DifferentiableAt ℂ F z)
    (hdecay : ∀ a ∈ Set.Icc σ σ₀, ∀ y : ℝ, ‖F ((a : ℂ) + y * I)‖ ≤ C * (1 + |y|) ^ (-p)) :
    (∀ a ∈ Set.Icc σ σ₀, Integrable (fun y : ℝ => smoothed σ c t F ((a : ℂ) + y * I))) ∧
    Tendsto (fun y : ℝ => ∫ a in σ..σ₀, smoothed σ c t F ((a : ℂ) + y * I)) atTop (𝓝 0) ∧
    Tendsto (fun y : ℝ => ∫ a in σ..σ₀, smoothed σ c t F ((a : ℂ) + y * I)) atBot (𝓝 0) ∧
    (∫ y : ℝ, smoothed σ c t F ((σ₀ : ℂ) + y * I)) =
      ∫ y : ℝ, smoothed σ c t F ((σ : ℂ) + y * I) := by
  let G := smoothed σ c t F
  have hG (z : ℂ) (ha : σ ≤ z.re) (hb : z.re ≤ σ₀) : DifferentiableAt ℂ G z := by
    have hden : (c : ℂ) + z - σ ≠ 0 := by
      intro hz
      have hr := congrArg Complex.re hz
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hr
      linarith
    have he : DifferentiableAt ℂ (fun w : ℂ => Complex.exp ((w - σ) * t)) z := by fun_prop
    have hnum : DifferentiableAt ℂ (fun _ : ℂ => (c : ℂ)) z := by fun_prop
    have hm : DifferentiableAt ℂ (fun w : ℂ => (c : ℂ) / ((c : ℂ) + w - σ)) z :=
      hnum.div (by fun_prop) hden
    exact (he.mul (hF z ⟨ha, hb⟩)).mul hm
  let A := Real.exp ((σ₀ - σ) * |t|) * C * (1 + c)
  let bound : ℝ → ℝ := fun y => A * (1 + |y|) ^ (-(p + 1))
  have hbound (a y : ℝ) (ha : σ ≤ a) (hb : a ≤ σ₀) :
      ‖G ((a : ℂ) + y * I)‖ ≤ bound y :=
    norm_smoothed_le t hc hC hdecay ⟨ha, hb⟩
  have hint : Integrable bound := by
    have h := integrable_one_add_norm (E := ℝ) (μ := volume)
      (r := p + 1) (by simpa using hp)
    simpa [bound, Real.norm_eq_abs] using h.const_mul A
  have htop : Tendsto bound atTop (𝓝 0) := by
    have hbase : Tendsto (fun y : ℝ => 1 + |y|) atTop atTop :=
      tendsto_atTop_add_const_left _ _ tendsto_abs_atTop_atTop
    simpa [bound] using
      ((tendsto_rpow_neg_atTop (show 0 < p + 1 by linarith)).comp hbase).const_mul A
  have hbot : Tendsto bound atBot (𝓝 0) := by
    simpa [bound, Function.comp_def] using htop.comp tendsto_neg_atBot_atTop
  have hhorizontal (y : ℝ) :
      ‖∫ a in σ..σ₀, G ((a : ℂ) + y * I)‖ ≤ bound y * |σ₀ - σ| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro a ha
    rw [Set.uIoc_of_le hσσ₀.le] at ha
    exact hbound a y ha.1.le ha.2
  refine ⟨fun a ha => Zeta23.WeilEF.integrable_line
    (fun y => hG _ (by simpa using ha.1) (by simpa using ha.2)) hint
    (fun y => hbound a y ha.1 ha.2), ?_, ?_, ?_⟩
  · exact squeeze_zero_norm hhorizontal (by simpa using htop.mul_const |σ₀ - σ|)
  · exact squeeze_zero_norm hhorizontal (by simpa using hbot.mul_const |σ₀ - σ|)
  · exact Zeta23.WeilEF.vertical_line_shift hσσ₀.le hG hint hbound htop hbot

end

end D5.S3.Analytic.Laplace.ExponentialMultiplierContour
