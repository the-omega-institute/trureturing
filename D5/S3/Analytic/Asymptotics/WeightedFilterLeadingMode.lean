/- GID: D5/S3/Analytic/Asymptotics/WeightedFilterLeadingMode
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/WeightedFilterLeadingMode
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The first Laplace moment bounds the error in the leading exponential. -/

import D5.S3.Analytic.Asymptotics.WeightedFilterCDF
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Leading exponential response of the Robin correction

The response averages the complex multiplier of one mode against the
Laplace measure. The first Laplace moment controls its error from the Robin weight.
-/

open MeasureTheory Set
open WeightedFilterCDF

noncomputable section

namespace WeightedFilterLeadingMode

/-- Bounds on the exponential moment of a probability supported on \([0,h]\). -/
theorem moment_bounds {μ : Measure ℝ} [IsProbabilityMeasure μ] {h y : ℝ}
    (hμ : ∀ᵐ u ∂μ, u ∈ Icc 0 h) (hy : 0 ≤ y) :
    1 ≤ moment μ y ∧ moment μ y ≤ Real.exp (h * y) := by
  have hbound : ∀ᵐ u ∂μ, Real.exp (y * u) ≤ Real.exp (h * y) := by
    filter_upwards [hμ] with u hu
    apply Real.exp_le_exp.mpr
    rw [mul_comm h y]
    exact mul_le_mul_of_nonneg_left hu.2 hy
  have hInt : Integrable (fun u => Real.exp (y * u)) μ := by
    apply Integrable.of_bound (by fun_prop) (Real.exp (h * y))
    filter_upwards [hbound] with u hu
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos (y * u))] using hu
  unfold moment
  constructor
  · calc
      1 = ∫ _u, (1 : ℝ) ∂μ := by simp
      _ ≤ _ := by
        apply integral_mono_ae (integrable_const _) hInt
        filter_upwards [hμ] with u hu
        exact Real.one_le_exp (mul_nonneg hy hu.1)
  · calc
      _ ≤ ∫ _u, Real.exp (h * y) ∂μ :=
        integral_mono_ae hInt (integrable_const _) hbound
      _ = _ := by simp

private theorem measurable_moment (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measurable (moment μ) := by
  have hm : StronglyMeasurable (fun z : ℝ × ℝ => Real.exp (z.1 * z.2)) :=
    (show Measurable (fun z : ℝ × ℝ => Real.exp (z.1 * z.2)) by
      fun_prop).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

/-- The multiplier of a single mode after the input moment correction. -/
def multiplier (μ : Measure ℝ) (lam : ℂ) (y : ℝ) : ℂ :=
  (-lam) / ((moment μ y : ℂ) * ((y : ℂ) - lam))

private theorem measurable_multiplier (μ : Measure ℝ) [IsProbabilityMeasure μ] (lam : ℂ) :
    Measurable (multiplier μ lam) := by
  unfold multiplier
  exact measurable_const.div
    ((Complex.measurable_ofReal.comp (measurable_moment μ)).mul
      (Complex.measurable_ofReal.sub measurable_const))

/-- The pointwise correction costs at most \((h+1/(-\operatorname{Re}\lambda))y\). -/
theorem norm_multiplier_sub_one_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {h y : ℝ} {lam : ℂ} (hμ : ∀ᵐ u ∂μ, u ∈ Icc 0 h)
    (hy : 0 ≤ y) (hlam : lam.re < 0) :
    ‖multiplier μ lam y - 1‖ ≤ (h + 1 / (-lam.re)) * y := by
  obtain ⟨hM₁, hM₂⟩ := moment_bounds hμ hy
  have hM : 0 < moment μ y := lt_of_lt_of_le zero_lt_one hM₁
  have hMne : (moment μ y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hM.ne'
  have hInv₀ : 0 ≤ (moment μ y)⁻¹ := inv_nonneg.mpr hM.le
  have hInv₁ : (moment μ y)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hM₁
  have hExpInv : Real.exp (-(h * y)) ≤ (moment μ y)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ hM hM₂
  have hInvError : 1 - (moment μ y)⁻¹ ≤ h * y := by
    linarith only [hExpInv, Real.add_one_le_exp (-(h * y))]
  have hD : -lam.re ≤ ‖(y : ℂ) - lam‖ := by
    have hre := Complex.re_le_norm ((y : ℂ) - lam)
    rw [Complex.sub_re, Complex.ofReal_re] at hre
    linarith only [hre, hy]
  have hDpos : 0 < ‖(y : ℂ) - lam‖ := (neg_pos.mpr hlam).trans_le hD
  have hDne : (y : ℂ) - lam ≠ 0 := norm_pos_iff.mp hDpos
  have hsplit :
      multiplier μ lam y - 1 =
        (((moment μ y)⁻¹ - 1 : ℝ) : ℂ) -
          (((moment μ y)⁻¹ : ℝ) : ℂ) * ((y : ℂ) / ((y : ℂ) - lam)) := by
    rw [multiplier, Complex.ofReal_sub, Complex.ofReal_one]
    simp only [Complex.ofReal_inv]
    field_simp [hMne, hDne]
    ring
  rw [hsplit]
  calc
    _ ≤ ‖(((moment μ y)⁻¹ - 1 : ℝ) : ℂ)‖ +
          ‖(((moment μ y)⁻¹ : ℝ) : ℂ) * ((y : ℂ) / ((y : ℂ) - lam))‖ :=
      norm_sub_le _ _
    _ = (1 - (moment μ y)⁻¹) + (moment μ y)⁻¹ * (y / ‖(y : ℂ) - lam‖) := by
      rw [norm_mul, norm_div]
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr hInv₁), neg_sub, abs_of_nonneg hInv₀, abs_of_nonneg hy]
    _ ≤ h * y + y / (-lam.re) := by
      apply add_le_add hInvError
      calc
        _ ≤ 1 * (y / ‖(y : ℂ) - lam‖) :=
          mul_le_mul_of_nonneg_right hInv₁ (div_nonneg hy hDpos.le)
        _ = y / ‖(y : ℂ) - lam‖ := one_mul _
        _ ≤ y / (-lam.re) := div_le_div_of_nonneg_left hy (neg_pos.mpr hlam) hD
    _ = (h + 1 / (-lam.re)) * y := by ring

private theorem laplace_monomial_integrable (n : ℕ) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun y : ℝ => y ^ n * Real.exp (-t * y)) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  simpa only [Real.rpow_one, Real.rpow_natCast] using
    integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (n : ℝ))
      (by linarith) (by norm_num) ht

private theorem integral_laplace_monomial (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ y : ℝ in Ici 0, y ^ n * Real.exp (-t * y)) =
      (1 / t) ^ (n + 1) * (n.factorial : ℝ) := by
  rw [integral_Ici_eq_integral_Ioi]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have H := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1)
    (by linarith) ht
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := Nat.cast_succ n
  rw [Real.Gamma_nat_eq_factorial, add_sub_cancel_right, ← hcast] at H
  simpa only [Real.rpow_natCast, ← neg_mul] using H

private theorem tail_laplace_moment (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun y : ℝ => y ^ n * Real.exp (-t * y)) tailMeasure ∧
      (∫ y : ℝ, y ^ n * Real.exp (-t * y) ∂tailMeasure) =
        (1 / t) ^ (n + 1) * (n.factorial : ℝ) +
          (1 / t) ^ (n + 2) * ((n + 1).factorial : ℝ) := by
  have h₀ := laplace_monomial_integrable n ht
  have h₁ := laplace_monomial_integrable (n + 1) ht
  have hdensity :
      (fun y : ℝ => (ENNReal.ofReal (1 + y)).toReal • (y ^ n * Real.exp (-t * y))) =ᵐ[
        volume.restrict (Ici (0 : ℝ))]
      (fun y => y ^ n * Real.exp (-t * y) + y ^ (n + 1) * Real.exp (-t * y)) := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ici (a := (0 : ℝ)))]
      with y hy
    have hy' : 0 ≤ 1 + y := by linarith [mem_Ici.mp hy]
    rw [ENNReal.toReal_ofReal hy', smul_eq_mul, pow_succ]
    ring
  constructor
  · unfold tailMeasure
    apply (integrable_withDensity_iff_integrable_smul' (by fun_prop) (by simp)).mpr
    exact (h₀.add h₁).congr hdensity.symm
  · rw [tailMeasure, integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp),
      integral_congr_ae hdensity, integral_add h₀ h₁,
      integral_laplace_monomial n ht, integral_laplace_monomial (n + 1) ht]

/-- The zeroth Laplace moment of the half-line measure is the Robin weight. -/
theorem integral_tail_exp {t : ℝ} (ht : 0 < t) :
    (∫ y, Real.exp (-t * y) ∂tailMeasure) = weight t := by
  have H := (tail_laplace_moment 0 ht).2
  norm_num [Nat.factorial] at H
  simp only [neg_mul]
  rw [H, weight]
  field_simp [ht.ne'] <;> ring

/-- The first Laplace moment of the half-line measure. -/
theorem integral_tail_first_moment {t : ℝ} (ht : 0 < t) :
    (∫ y, y * Real.exp (-t * y) ∂tailMeasure) = 1 / t ^ 2 + 2 / t ^ 3 := by
  have H := (tail_laplace_moment 1 ht).2
  norm_num [Nat.factorial] at H
  simp only [neg_mul]
  rw [H]
  field_simp [ht.ne'] <;> ring

private theorem first_moment_le {t : ℝ} (ht : 0 < t) :
    1 / t ^ 2 + 2 / t ^ 3 ≤ 2 * (weight t / t) := by
  have heq : 2 * (weight t / t) - (1 / t ^ 2 + 2 / t ^ 3) = 1 / t ^ 2 := by
    unfold weight
    field_simp [ht.ne']
    ring
  have hn : 0 ≤ (1 : ℝ) / t ^ 2 := by positivity
  linarith only [heq, hn]

private theorem tailMeasure_mem : ∀ᵐ y ∂tailMeasure, y ∈ Ici (0 : ℝ) :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ici)

/-- The Laplace response after factoring out the value of the mode at t. -/
def response (μ : Measure ℝ) (lam : ℂ) (t : ℝ) : ℂ :=
  ∫ y, (Real.exp (-t * y) : ℂ) * multiplier μ lam y ∂tailMeasure

/-- The response with the density of the half-line measure exposed. -/
theorem response_eq_integral_Ici (μ : Measure ℝ) (lam : ℂ) (t : ℝ) :
    response μ lam t = ∫ y : ℝ in Ici 0,
      (((1 + y) * Real.exp (-t * y) : ℝ) : ℂ) * multiplier μ lam y := by
  rw [response, tailMeasure, integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp)]
  apply setIntegral_congr_fun measurableSet_Ici
  intro y hy
  change (ENNReal.ofReal (1 + y)).toReal •
      ((Real.exp (-t * y) : ℂ) * multiplier μ lam y) =
    (((1 + y) * Real.exp (-t * y) : ℝ) : ℂ) * multiplier μ lam y
  rw [ENNReal.toReal_ofReal (by linarith [mem_Ici.mp hy]), Complex.real_smul,
    Complex.ofReal_mul, mul_assoc]

/-- Integrating the multiplier error gives its exact first-moment bound. -/
theorem norm_response_sub_weight_le_first_moment
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {h t : ℝ} {lam : ℂ}
    (hμ : ∀ᵐ u ∂μ, u ∈ Icc 0 h) (ht : 0 < t) (hlam : lam.re < 0) :
    ‖response μ lam t - (weight t : ℂ)‖ ≤
      (h + 1 / (-lam.re)) * (1 / t ^ 2 + 2 / t ^ 3) := by
  let c : ℝ := h + 1 / (-lam.re)
  let e : ℝ → ℂ := fun y => (Real.exp (-t * y) : ℂ)
  let g : ℝ → ℂ := fun y => e y * (multiplier μ lam y - 1)
  have heMeas : Measurable e := Complex.measurable_ofReal.comp
    (show Measurable (fun y : ℝ => Real.exp (-t * y)) by fun_prop)
  have he : Integrable e tailMeasure := by
    apply (tail_laplace_moment 0 ht).1.mono' heMeas.aestronglyMeasurable
    exact ae_of_all _ fun y => by
      change ‖(Real.exp (-t * y) : ℂ)‖ ≤ y ^ (0 : ℕ) * Real.exp (-t * y)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_zero, one_mul]
  have hdom : Integrable (fun y => c * (y * Real.exp (-t * y))) tailMeasure := by
    simpa only [pow_one] using (tail_laplace_moment 1 ht).1.const_mul c
  have hbound : ∀ᵐ y ∂tailMeasure, ‖g y‖ ≤ c * (y * Real.exp (-t * y)) := by
    filter_upwards [tailMeasure_mem] with y hy
    change ‖(Real.exp (-t * y) : ℂ) * (multiplier μ lam y - 1)‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-t * y) * (c * y) :=
        mul_le_mul_of_nonneg_left (norm_multiplier_sub_one_le hμ (mem_Ici.mp hy) hlam)
          (Real.exp_pos _).le
      _ = _ := by ring
  have hgMeas : Measurable g :=
    heMeas.mul ((measurable_multiplier μ lam).sub measurable_const)
  have hg : Integrable g tailMeasure := hdom.mono' hgMeas.aestronglyMeasurable hbound
  have hsplit : (fun y => e y * multiplier μ lam y) = fun y => g y + e y := by
    funext y
    dsimp only [g]
    ring
  have heq : (∫ y, e y ∂tailMeasure) = (weight t : ℂ) := by
    change (∫ y, (Real.exp (-t * y) : ℂ) ∂tailMeasure) = _
    rw [integral_complex_ofReal, integral_tail_exp ht]
  have herror : response μ lam t - (weight t : ℂ) = ∫ y, g y ∂tailMeasure := by
    change (∫ y, e y * multiplier μ lam y ∂tailMeasure) - (weight t : ℂ) = _
    rw [hsplit, integral_add hg he, heq, add_sub_cancel_right]
  rw [herror]
  calc
    _ ≤ ∫ y, c * (y * Real.exp (-t * y)) ∂tailMeasure :=
      norm_integral_le_of_norm_le hdom hbound
    _ = _ := by rw [integral_const_mul, integral_tail_first_moment ht]

/-- The error is bounded by an explicit multiple of the Robin weight divided by t. -/
theorem norm_response_sub_weight_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {h t : ℝ} {lam : ℂ} (hμ : ∀ᵐ u ∂μ, u ∈ Icc 0 h) (ht : 0 < t) (hlam : lam.re < 0) :
    ‖response μ lam t - (weight t : ℂ)‖ ≤
      2 * (h + 1 / (-lam.re)) * (weight t / t) := by
  obtain ⟨u, hu⟩ := hμ.exists
  have hh : 0 ≤ h := hu.1.trans hu.2
  have hc : 0 ≤ h + 1 / (-lam.re) := add_nonneg hh (one_div_nonneg.mpr (neg_nonneg.mpr hlam.le))
  calc
    _ ≤ (h + 1 / (-lam.re)) * (1 / t ^ 2 + 2 / t ^ 3) :=
      norm_response_sub_weight_le_first_moment hμ ht hlam
    _ ≤ (h + 1 / (-lam.re)) * (2 * (weight t / t)) :=
      mul_le_mul_of_nonneg_left (first_moment_le ht) hc
    _ = _ := by ring

/-- The error bound with the complex amplitude and the mode at t restored. -/
theorem norm_leading_mode_error_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {h t : ℝ} {lam : ℂ} (hμ : ∀ᵐ u ∂μ, u ∈ Icc 0 h) (ht : 0 < t) (hlam : lam.re < 0)
    (C : ℂ) :
    ‖C * Complex.exp (lam * (t : ℂ)) * response μ lam t -
      C * Complex.exp (lam * (t : ℂ)) * (weight t : ℂ)‖ ≤
      ‖C‖ * Real.exp (lam.re * t) * (2 * (h + 1 / (-lam.re)) * (weight t / t)) := by
  have hre : (lam * (t : ℂ)).re = lam.re * t := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [← mul_sub, norm_mul, norm_mul, Complex.norm_exp, hre]
  exact mul_le_mul_of_nonneg_left (norm_response_sub_weight_le hμ ht hlam)
    (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)

end WeightedFilterLeadingMode
