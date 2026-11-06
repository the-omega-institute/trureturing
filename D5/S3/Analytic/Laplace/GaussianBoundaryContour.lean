/- GID: D5/S3/Analytic/Laplace/GaussianBoundaryContour
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/GaussianBoundaryContour
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A quadratic strip bound permits Gaussian contour shifts and cubic Gaussian bounds. -/

import D5.S3.Analytic.Laplace.GaussianStripControl
import D5.S3.Analytic.Fourier.GaussianKernel
import D5.S3.Analytic.Asymptotics.BarnesResidue

/-! Gaussian contour shifting and quantitative estimates for a regular Laplace term. -/

namespace D5.S3.Analytic.Laplace.GaussianBoundary

open D5.S3.Analytic.Laplace.PairedPoleRegularity
open MeasureTheory Set Filter
open scoped Topology

noncomputable section

lemma gaussian_polynomial_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun t : ℝ => (1 + |t|) ^ 2 * Real.exp (-b * t ^ 2)) := by
  have hi := integrable_rpow_mul_exp_neg_mul_sq hb (show (-1 : ℝ) < 2 by norm_num)
  simp only [Real.rpow_two] at hi
  apply (((integrable_exp_neg_mul_sq hb).add hi).const_mul 2).mono' (by fun_prop)
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have ht := sq_nonneg (|t| - 1)
  have ht2 : |t| ^ 2 = t ^ 2 := sq_abs t
  change (1 + |t|) ^ 2 * Real.exp (-b * t ^ 2) ≤
    2 * (Real.exp (-b * t ^ 2) + t ^ 2 * Real.exp (-b * t ^ 2))
  have hp : (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by nlinarith
  calc
    _ ≤ 2 * (1 + t ^ 2) * Real.exp (-b * t ^ 2) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
    _ = _ := by ring

lemma gaussian_exponent_re (M c y t : ℝ) :
    ((((c : ℂ) + t * Complex.I) * y +
      ((c : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2)).re) =
        c * y + (c ^ 2 - t ^ 2) / (2 * M ^ 2) := by
  rw [D5.S3.Analytic.Fourier.GaussianKernel.bromwich_exponent]
  have hcoeff : -(1 / (2 * (M : ℂ) ^ 2)) = ((-(1 / (2 * M ^ 2)) : ℝ) : ℂ) := by
    push_cast <;> rfl
  have hlinear : (y : ℂ) + c / M ^ 2 = ((y + c / M ^ 2 : ℝ) : ℂ) := by
    push_cast <;> rfl
  have hconst : (c : ℂ) * y + c ^ 2 / (2 * M ^ 2) =
      ((c * y + c ^ 2 / (2 * M ^ 2) : ℝ) : ℂ) := by
    push_cast <;> rfl
  rw [hcoeff, hlinear, hconst]
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
    zero_add, add_zero, sub_zero]
  ring

/-- The Gaussian damps every quadratically bounded holomorphic function on a vertical line. -/
theorem regular_vertical_integrable {J : ℂ → ℂ} (hstrip : GaussianStripControl J)
    {M : ℝ} (hM : 0 < M) (y : ℝ) {c : ℝ}
    (hc₁ : -(1 / 6 : ℝ) ≤ c) (hc₂ : c ≤ 3 / 4) :
    Integrable (fun t : ℝ => J ((c : ℂ) + t * Complex.I) *
      Complex.exp (((c : ℂ) + t * Complex.I) * y +
        ((c : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2))) := by
  obtain ⟨C, hC, hbound⟩ := hstrip.growth
  have hc : Continuous (fun t : ℝ => J ((c : ℂ) + t * Complex.I)) := by
    apply hstrip.holomorphic.continuousOn.comp_continuous (by fun_prop)
    intro t
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, Set.mem_ofPred_eq]
    constructor <;> linarith
  apply ((gaussian_polynomial_integrable (show 0 < 1 / (2 * M ^ 2) by positivity)).const_mul
    (C * Real.exp (c * y + c ^ 2 / (2 * M ^ 2)))).mono'
      (hc.mul (by fun_prop)).aestronglyMeasurable
  filter_upwards with t
  simp only [Pi.mul_apply]
  rw [norm_mul, Complex.norm_exp, gaussian_exponent_re]
  have hb := hbound ((c : ℂ) + t * Complex.I) (by simpa using hc₁) (by simpa using hc₂)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at hb
  calc
    _ ≤ C * (1 + |t|) ^ 2 * Real.exp (c * y + (c ^ 2 - t ^ 2) / (2 * M ^ 2)) :=
      mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
    _ = _ := by
      rw [show c * y + (c ^ 2 - t ^ 2) / (2 * M ^ 2) =
        (c * y + c ^ 2 / (2 * M ^ 2)) + -(1 / (2 * M ^ 2)) * t ^ 2 by ring,
        Real.exp_add]
      ring


private lemma regular_horizontal_norm {J : ℂ → ℂ} {C M y c t : ℝ}
    (hC : 0 ≤ C) (hM : 0 < M)
    (hbound : ∀ s : ℂ, -(1 / 6 : ℝ) ≤ s.re → s.re ≤ 3 / 4 →
      ‖J s‖ ≤ C * (1 + |s.im|) ^ 2)
    (hc₁ : -(1 / 6 : ℝ) ≤ c) (hc₂ : c ≤ 3 / 4) :
    ‖J ((c : ℂ) + t * Complex.I) *
      Complex.exp (((c : ℂ) + t * Complex.I) * y +
        ((c : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2))‖ ≤
      (C * Real.exp (|y| + 1 / (2 * M ^ 2))) *
        ((1 + |t|) ^ 2 * Real.exp (-(1 / (2 * M ^ 2)) * t ^ 2)) := by
  rw [norm_mul, Complex.norm_exp, gaussian_exponent_re]
  have hb := hbound ((c : ℂ) + t * Complex.I) (by simpa using hc₁) (by simpa using hc₂)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at hb
  have hcabs : |c| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hcy : c * y ≤ |y| := (le_abs_self _).trans (by
    rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hcabs)
  have hc2 : c ^ 2 ≤ 1 := by nlinarith [sq_abs c, abs_nonneg c]
  calc
    _ ≤ (C * (1 + |t|) ^ 2) *
        Real.exp ((|y| + 1 / (2 * M ^ 2)) + -(1 / (2 * M ^ 2)) * t ^ 2) := by
      apply mul_le_mul hb _ (Real.exp_nonneg _) (by positivity)
      apply Real.exp_le_exp.mpr
      have hd := div_le_div_of_nonneg_right hc2 (show 0 ≤ 2 * M ^ 2 by positivity)
      convert add_le_add_right (add_le_add hcy hd) (-(1 / (2 * M ^ 2)) * t ^ 2) using 1 <;> ring
    _ = _ := by rw [Real.exp_add]; ring

private lemma gaussian_polynomial_tendsto {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => (1 + |t|) ^ 2 * Real.exp (-b * t ^ 2)) atTop (𝓝 0) := by
  have hs : Tendsto (fun t : ℝ => t ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have h₀ := Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr hb)).2 hs)
  have h₂ := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 b hb).comp hs
  simp only [Real.rpow_one, Function.comp_def] at h₂
  apply squeeze_zero' (Eventually.of_forall (fun t => by positivity)) _
    (show Tendsto (fun t : ℝ => 2 * (Real.exp (-b * t ^ 2) +
      t ^ 2 * Real.exp (-b * t ^ 2))) atTop (𝓝 0) by simpa using (h₀.add h₂).const_mul 2)
  filter_upwards with t
  have hp : (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by
    nlinarith [sq_nonneg (|t| - 1), sq_abs t]
  nlinarith [mul_le_mul_of_nonneg_right hp (Real.exp_nonneg (-b * t ^ 2))]

/-- Gaussian damping makes the horizontal cross-sections vanish at either end of the strip. -/
private theorem regular_horizontal_tendsto {J : ℂ → ℂ} (hstrip : GaussianStripControl J)
    {M : ℝ} (hM : 0 < M) (y : ℝ) :
    Tendsto (fun t : ℝ => ∫ c in -(1 / 6 : ℝ)..(3 / 4 : ℝ),
      J ((c : ℂ) + t * Complex.I) *
        Complex.exp (((c : ℂ) + t * Complex.I) * y +
          ((c : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2))) atTop (𝓝 0) ∧
    Tendsto (fun t : ℝ => ∫ c in -(1 / 6 : ℝ)..(3 / 4 : ℝ),
      J ((c : ℂ) + t * Complex.I) *
        Complex.exp (((c : ℂ) + t * Complex.I) * y +
          ((c : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2))) atBot (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := hstrip.growth
  let B := (C * Real.exp (|y| + 1 / (2 * M ^ 2))) * |(3 / 4 : ℝ) - -(1 / 6 : ℝ)|
  have hb (t : ℝ) :
      ‖∫ c in -(1 / 6 : ℝ)..(3 / 4 : ℝ), J ((c : ℂ) + t * Complex.I) *
        Complex.exp (((c : ℂ) + t * Complex.I) * y +
          ((c : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2))‖ ≤
        B * ((1 + |t|) ^ 2 * Real.exp (-(1 / (2 * M ^ 2)) * t ^ 2)) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -(1 / 6 : ℝ)) (b := (3 / 4 : ℝ))
      (C := (C * Real.exp (|y| + 1 / (2 * M ^ 2))) *
        ((1 + |t|) ^ 2 * Real.exp (-(1 / (2 * M ^ 2)) * t ^ 2)))
      (fun c hc => regular_horizontal_norm hC hM hbound
        (by simpa only [min_eq_left (show -(1 / 6 : ℝ) ≤ 3 / 4 by norm_num)] using hc.1.le)
        (by simpa only [max_eq_right (show -(1 / 6 : ℝ) ≤ 3 / 4 by norm_num)] using hc.2))
    convert hh using 1; dsimp [B]; ring
  have ht := (gaussian_polynomial_tendsto (show 0 < 1 / (2 * M ^ 2) by positivity)).const_mul B
  simp only [mul_zero] at ht
  constructor
  · exact squeeze_zero_norm hb ht
  · have ht' := ht.comp tendsto_neg_atBot_atTop
    simp only [Function.comp_def, abs_neg, neg_sq] at ht'
    exact squeeze_zero_norm hb ht'


/-- The holomorphic regular term can be moved from real part three quarters to minus one sixth. -/
private theorem regular_vertical_shift {J : ℂ → ℂ} (hstrip : GaussianStripControl J)
    {M : ℝ} (hM : 0 < M) (y : ℝ) :
    (∫ t : ℝ, J (((3 / 4 : ℝ) : ℂ) + t * Complex.I) *
      Complex.exp ((((3 / 4 : ℝ) : ℂ) + t * Complex.I) * y +
        (((3 / 4 : ℝ) : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2))) =
    ∫ t : ℝ, J (((-(1 / 6) : ℝ) : ℂ) + t * Complex.I) *
      Complex.exp ((((-(1 / 6) : ℝ) : ℂ) + t * Complex.I) * y +
        (((-(1 / 6) : ℝ) : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2)) := by
  let F : ℂ → ℂ := fun s => J s * Complex.exp (s * y + s ^ 2 / (2 * M ^ 2))
  let φ : ℂ → ℂ := fun s => s * F s
  have hφ : DifferentiableOn ℂ φ (Complex.re ⁻¹' Icc (-(1 / 6 : ℝ)) (3 / 4 : ℝ)) := by
    apply differentiableOn_id.mul
    apply (hstrip.holomorphic.mono ?_).mul
    · fun_prop
    · intro s hs
      change -(1 / 6 : ℝ) ≤ s.re ∧ s.re ≤ 3 / 4 at hs
      constructor <;> linarith [hs.1, hs.2]
  have he (s : ℂ) (hs : s ≠ 0) : φ s / (s - 0) = F s := by
    dsimp [φ]
    rw [sub_zero, mul_div_cancel_left₀ _ hs]
  have hne (c t : ℝ) (hc : c ≠ 0) : (c : ℂ) + t * Complex.I ≠ 0 := by
    intro hh
    apply hc
    simpa using congrArg Complex.re hh
  have hi₁ : Integrable (fun t : ℝ => φ (((-(1 / 6) : ℝ) : ℂ) + t * Complex.I) /
      (((-(1 / 6) : ℝ) : ℂ) + t * Complex.I - 0)) := by
    convert regular_vertical_integrable hstrip hM y (c := -(1 / 6)) le_rfl (by norm_num) using 1
    ext t
    exact he _ (hne (-(1 / 6)) t (by norm_num))
  have hi₂ : Integrable (fun t : ℝ => φ (((3 / 4 : ℝ) : ℂ) + t * Complex.I) /
      (((3 / 4 : ℝ) : ℂ) + t * Complex.I - 0)) := by
    convert regular_vertical_integrable hstrip hM y (c := 3 / 4) (by norm_num) le_rfl using 1
    ext t
    exact he _ (hne (3 / 4) t (by norm_num))
  have hedge := regular_horizontal_tendsto hstrip hM y
  have hedgetop : Tendsto (fun t : ℝ => ∫ c in -(1 / 6 : ℝ)..(3 / 4 : ℝ),
      φ ((c : ℂ) + t * Complex.I) / ((c : ℂ) + t * Complex.I - 0)) atTop (𝓝 0) := by
    apply hedge.1.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    apply intervalIntegral.integral_congr
    intro c hc
    exact (he _ (by intro hh; have := congrArg Complex.im hh; simp at this; linarith)).symm
  have hedgebot : Tendsto (fun t : ℝ => ∫ c in -(1 / 6 : ℝ)..(3 / 4 : ℝ),
      φ ((c : ℂ) + t * Complex.I) / ((c : ℂ) + t * Complex.I - 0)) atBot (𝓝 0) := by
    apply hedge.2.congr'
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
    apply intervalIntegral.integral_congr
    intro c hc
    exact (he _ (by intro hh; have := congrArg Complex.im hh; simp at this; linarith)).symm
  have h := D5.S3.Analytic.Asymptotics.BarnesResidue.barnesRes_vertical_shift
    (p := 0) (by norm_num : -(1 / 6 : ℝ) < (0 : ℂ).re)
    (by norm_num : (0 : ℂ).re < (3 / 4 : ℝ)) hφ hi₁ hi₂ hedgetop hedgebot
  have hh : φ 0 = 0 := by simp [φ]
  rw [hh, mul_zero, sub_eq_zero] at h
  simpa only [he _ (hne (3 / 4) _ (by norm_num)),
    he _ (hne (-(1 / 6)) _ (by norm_num)), F] using h


private lemma gaussian_polynomial_integral_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℝ, 1 ≤ M →
      (∫ t : ℝ, (1 + |t|) ^ 2 * Real.exp (-(1 / (2 * M ^ 2)) * t ^ 2)) ≤ K * M ^ 3 := by
  let g : ℝ → ℝ := fun t => (1 + |t|) ^ 2 * Real.exp (-(1 / 2 : ℝ) * t ^ 2)
  refine ⟨∫ t, g t, integral_nonneg (fun t => by dsimp [g]; positivity), ?_⟩
  intro M hM
  have hM0 : 0 < M := by linarith
  let gM : ℝ → ℝ := fun t => (1 + |t|) ^ 2 * Real.exp (-(1 / (2 * M ^ 2)) * t ^ 2)
  have hi := gaussian_polynomial_integrable (show 0 < 1 / (2 * M ^ 2) by positivity)
  have hgi : Integrable g := gaussian_polynomial_integrable (by norm_num)
  have hle (t : ℝ) : gM (M * t) ≤ M ^ 2 * g t := by
    dsimp [gM, g]
    rw [abs_mul, abs_of_pos hM0]
    have he : -(1 / (2 * M ^ 2)) * (M * t) ^ 2 = -(1 / 2 : ℝ) * t ^ 2 := by
      field_simp
    rw [he]
    have hh : (1 + M * |t|) ^ 2 ≤ (M * (1 + |t|)) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [abs_nonneg t]
    calc
      _ ≤ (M * (1 + |t|)) ^ 2 * Real.exp (-(1 / 2 : ℝ) * t ^ 2) :=
        mul_le_mul_of_nonneg_right hh (Real.exp_nonneg _)
      _ = _ := by ring
  calc
    _ = M * (∫ t, gM (M * t)) := by
      rw [Measure.integral_comp_mul_left, smul_eq_mul, abs_of_pos (inv_pos.mpr hM0)]
      simp only [gM]
      field_simp
    _ ≤ M * (∫ t, M ^ 2 * g t) :=
      mul_le_mul_of_nonneg_left (integral_mono (hi.comp_mul_left' hM0.ne')
        (hgi.const_mul _) hle) hM0.le
    _ = _ := by rw [integral_const_mul]; ring

/-- The Gaussian integral of the regular term is bounded by a cubic power of the scale. -/
theorem gaussian_regular_bound {J : ℂ → ℂ} (hstrip : GaussianStripControl J) :
    ∃ C : ℝ, 0 < C ∧ ∀ M y : ℝ, 1 ≤ M →
      ‖(1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ, J (((3 / 4 : ℝ) : ℂ) + t * Complex.I) *
          Complex.exp ((((3 / 4 : ℝ) : ℂ) + t * Complex.I) * y +
            (((3 / 4 : ℝ) : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2))‖ ≤
        C * M ^ 3 * Real.exp (-y / 6) := by
  obtain ⟨B, hB, hbound⟩ := hstrip.growth
  obtain ⟨K, hK, hmoment⟩ := gaussian_polynomial_integral_bound
  let N : ℝ := ‖(1 / (2 * Real.pi) : ℂ)‖
  refine ⟨N * (B * Real.exp 1 * K) + 1, by dsimp [N]; positivity, ?_⟩
  intro M y hM
  have hM0 : 0 < M := by linarith
  rw [regular_vertical_shift hstrip hM0 y, norm_mul]
  have hi := regular_vertical_integrable hstrip hM0 y (c := -(1 / 6)) le_rfl (by norm_num)
  let gM : ℝ → ℝ := fun t => (1 + |t|) ^ 2 * Real.exp (-(1 / (2 * M ^ 2)) * t ^ 2)
  have hgi : Integrable gM := gaussian_polynomial_integrable (by positivity)
  have hpt (t : ℝ) :
      ‖J (((-(1 / 6) : ℝ) : ℂ) + t * Complex.I) *
        Complex.exp ((((-(1 / 6) : ℝ) : ℂ) + t * Complex.I) * y +
          (((-(1 / 6) : ℝ) : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2))‖ ≤
      (B * Real.exp 1 * Real.exp (-y / 6)) * gM t := by
    rw [norm_mul, Complex.norm_exp]
    have hre := gaussian_exponent_re M (-(1 / 6)) y t
    rw [hre]
    have hb := hbound (((-(1 / 6) : ℝ) : ℂ) + t * Complex.I) (by norm_num) (by norm_num)
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at hb
    have hden : (-(1 / 6 : ℝ)) ^ 2 / (2 * M ^ 2) ≤ 1 := by
      apply (div_le_one (by positivity : 0 < 2 * M ^ 2)).mpr
      nlinarith
    calc
      _ ≤ (B * (1 + |t|) ^ 2) *
          Real.exp ((1 + -y / 6) + -(1 / (2 * M ^ 2)) * t ^ 2) := by
        apply mul_le_mul hb _ (Real.exp_nonneg _) (by positivity)
        apply Real.exp_le_exp.mpr
        convert add_le_add_right hden (-y / 6 - (1 / (2 * M ^ 2)) * t ^ 2) using 1 <;> ring
      _ = _ := by dsimp [gM]; rw [Real.exp_add, Real.exp_add]; ring
  calc
    _ ≤ N * (∫ t : ℝ, (B * Real.exp 1 * Real.exp (-y / 6)) * gM t) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact norm_integral_le_integral_norm _ |>.trans
        (integral_mono hi.norm (hgi.const_mul _) hpt)
    _ = N * (B * Real.exp 1) * Real.exp (-y / 6) * (∫ t, gM t) := by
      rw [integral_const_mul]; ring
    _ ≤ N * (B * Real.exp 1) * Real.exp (-y / 6) * (K * M ^ 3) :=
      mul_le_mul_of_nonneg_left (hmoment M hM) (by dsimp [N]; positivity)
    _ = (N * (B * Real.exp 1 * K)) * (M ^ 3 * Real.exp (-y / 6)) := by ring
    _ ≤ (N * (B * Real.exp 1 * K) + 1) * (M ^ 3 * Real.exp (-y / 6)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

end
end D5.S3.Analytic.Laplace.GaussianBoundary
