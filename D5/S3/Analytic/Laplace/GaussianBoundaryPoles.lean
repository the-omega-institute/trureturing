/- GID: D5/S3/Analytic/Laplace/GaussianBoundaryPoles
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/GaussianBoundaryPoles
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An inverse-square majorant permits Gaussian integration of paired pole series. -/

import D5.S3.Analytic.Laplace.GaussianBoundaryContour
import D5.S3.Analytic.Laplace.PairedPoleRegularity
import D5.S3.Analytic.Oscillation.GaussianSpectrum
import D5.S3.Analytic.Fourier.GaussianKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace D5.S3.Analytic.Laplace.GaussianBoundary

open D5.S3.Analytic.Laplace.PairedPoleRegularity
  D5.S3.Analytic.Oscillation.OrdinateCounting
  D5.S3.Analytic.Oscillation.GaussianSpectrum
open MeasureTheory Set Filter
open scoped Topology BigOperators

noncomputable section

private lemma pole_vertical_crude (S : Spectrum) (j : S.index) (t : ℝ) :
    ‖poleTerm S j ((3 / 4 : ℂ) + t * Complex.I)‖ ≤ 4 * (S.mult j : ℝ) := by
  let s : ℂ := (3 / 4 : ℂ) + t * Complex.I
  have hm : (3 / 4 : ℝ) ≤ ‖s - (S.gamma j : ℂ) * Complex.I‖ := by
    have h := Complex.abs_re_le_norm (s - (S.gamma j : ℂ) * Complex.I)
    norm_num [s] at h ⊢
    exact h
  have hp : (3 / 4 : ℝ) ≤ ‖s + (S.gamma j : ℂ) * Complex.I‖ := by
    have h := Complex.abs_re_le_norm (s + (S.gamma j : ℂ) * Complex.I)
    norm_num [s] at h ⊢
    exact h
  have hm' : ‖(1 : ℂ) / (s - (S.gamma j : ℂ) * Complex.I)‖ ≤ 2 := by
    rw [norm_div, norm_one]
    exact (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hp' : ‖(1 : ℂ) / (s + (S.gamma j : ℂ) * Complex.I)‖ ≤ 2 := by
    rw [norm_div, norm_one]
    exact (div_le_iff₀ (by linarith)).mpr (by linarith)
  change ‖poleTerm S j s‖ ≤ _
  unfold poleTerm
  rw [norm_mul, Complex.norm_natCast]
  have hn := norm_add_le ((1 : ℂ) / (s - (S.gamma j : ℂ) * Complex.I))
    ((1 : ℂ) / (s + (S.gamma j : ℂ) * Complex.I))
  calc
    _ ≤ (S.mult j : ℝ) * (2 + 2) := mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- Every pole pair has a common quadratic majorant weighted by its inverse-square mass. -/
private lemma pole_vertical_bound (S : Spectrum) (j : S.index) (t : ℝ) :
    ‖poleTerm S j ((3 / 4 : ℂ) + t * Complex.I)‖ ≤
      32 * (1 + |t|) ^ 2 * ((S.mult j : ℝ) / S.gamma j ^ 2) := by
  let s : ℂ := (3 / 4 : ℂ) + t * Complex.I
  have hs : ‖s‖ ≤ 1 + |t| := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    norm_num [s] at h
    linarith
  by_cases hg : ‖s‖ ≤ 3 * S.gamma j / 4
  · apply (pole_bound S j hg).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have ht := abs_nonneg t
    nlinarith
  · have hg' : S.gamma j ≤ 2 * (1 + |t|) := by linarith [abs_nonneg t]
    have hgsq : S.gamma j ^ 2 ≤ 4 * (1 + |t|) ^ 2 := by
      nlinarith [S.gamma_pos j, sq_nonneg (S.gamma j - 2 * (1 + |t|))]
    apply (pole_vertical_crude S j t).trans
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos (S.gamma_pos j))).mpr
    convert (show 4 * (S.mult j : ℝ) * S.gamma j ^ 2 ≤
        32 * (1 + |t|) ^ 2 * (S.mult j : ℝ) from by
      nlinarith [mul_le_mul_of_nonneg_left hgsq (Nat.cast_nonneg (S.mult j))]) using 1

private lemma gaussian_exp_norm (M y t : ℝ) :
    ‖Complex.exp (((3 / 4 : ℂ) + t * Complex.I) * y +
      ((3 / 4 : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2))‖ =
      Real.exp ((3 / 4 : ℝ) * y + (3 / 4 : ℝ) ^ 2 / (2 * M ^ 2)) *
        Real.exp (-(1 / (2 * M ^ 2)) * t ^ 2) := by
  have he := gaussian_exponent_re M (3 / 4) y t
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at he
  rw [Complex.norm_exp, he, ← Real.exp_add]
  congr 1
  ring


private lemma pole_gaussian_polynomial_integrable {M : ℝ} (hM : 0 < M) (y : ℝ) :
    Integrable (fun t : ℝ => 32 * (1 + |t|) ^ 2 *
      ‖Complex.exp (((3 / 4 : ℂ) + t * Complex.I) * y +
        ((3 / 4 : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2))‖) := by
  have hi := (gaussian_polynomial_integrable
    (show 0 < 1 / (2 * M ^ 2) by positivity)).const_mul
      (32 * Real.exp ((3 / 4 : ℝ) * y + (3 / 4 : ℝ) ^ 2 / (2 * M ^ 2)))
  convert hi using 1
  funext t
  rw [gaussian_exp_norm]
  ring

private lemma pole_gaussian_measurable (S : Spectrum) (j : S.index) (M y : ℝ) :
    AEStronglyMeasurable (fun t : ℝ =>
      poleTerm S j ((3 / 4 : ℂ) + t * Complex.I) *
        Complex.exp (((3 / 4 : ℂ) + t * Complex.I) * y +
          ((3 / 4 : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2))) := by
  unfold poleTerm
  fun_prop

/-- Each paired pole is absolutely integrable after multiplication by the Gaussian. -/
private lemma pole_gaussian_integrable (S : Spectrum) (j : S.index) {M : ℝ}
    (hM : 0 < M) (y : ℝ) :
    Integrable (fun t : ℝ => poleTerm S j ((3 / 4 : ℂ) + t * Complex.I) *
      Complex.exp (((3 / 4 : ℂ) + t * Complex.I) * y +
        ((3 / 4 : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2))) := by
  apply ((pole_gaussian_polynomial_integrable hM y).mul_const
    ((S.mult j : ℝ) / S.gamma j ^ 2)).mono' (pole_gaussian_measurable S j M y)
  filter_upwards with t
  rw [norm_mul]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_right (pole_vertical_bound S j t)
      (norm_nonneg (Complex.exp (((3 / 4 : ℂ) + t * Complex.I) * y +
        ((3 / 4 : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2))))



/-- The entire paired-pole series remains absolutely integrable on the Gaussian inversion line. -/
theorem pole_gaussian_tsum_integrable (S : Spectrum) (hN : CountAsymptotic S)
    {M : ℝ} (hM : 0 < M) (y : ℝ) :
    Integrable (fun t : ℝ => (∑' j : S.index, poleTerm S j ((3 / 4 : ℂ) + t * Complex.I)) *
      Complex.exp (((3 / 4 : ℂ) + t * Complex.I) * y +
        ((3 / 4 : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2))) := by
  have : Countable S.index := spectrum_countable S
  let W : ℝ := ∑' j : S.index, (S.mult j : ℝ) / S.gamma j ^ 2
  have hm : Measurable (fun t : ℝ => ∑' j : S.index,
      poleTerm S j ((3 / 4 : ℂ) + t * Complex.I)) :=
    Measurable.tsum (fun j => by unfold poleTerm; fun_prop)
  apply ((pole_gaussian_polynomial_integrable hM y).mul_const W).mono'
    (hm.mul (by fun_prop)).aestronglyMeasurable
  filter_upwards with t
  have hw := (inverse_square_summable S hN).mul_left (32 * (1 + |t|) ^ 2)
  have hnorm : Summable (fun j : S.index =>
      ‖poleTerm S j ((3 / 4 : ℂ) + t * Complex.I)‖) :=
    hw.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => pole_vertical_bound S j t)
  have hsum : ‖∑' j : S.index, poleTerm S j ((3 / 4 : ℂ) + t * Complex.I)‖ ≤
      32 * (1 + |t|) ^ 2 * W := by
    apply (norm_tsum_le_tsum_norm hnorm).trans
    simpa only [W, tsum_mul_left] using
      hnorm.tsum_le_tsum (fun j => pole_vertical_bound S j t) hw
  simp only [Pi.mul_apply]
  rw [norm_mul]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_right hsum (norm_nonneg (Complex.exp
      (((3 / 4 : ℂ) + t * Complex.I) * y +
        ((3 / 4 : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2))))

private lemma pole_gaussian_integral_norm_summable (S : Spectrum) (hN : CountAsymptotic S)
    {M : ℝ} (hM : 0 < M) (y : ℝ) :
    Summable (fun j : S.index => ∫ t : ℝ,
      ‖poleTerm S j ((3 / 4 : ℂ) + t * Complex.I) *
        Complex.exp (((3 / 4 : ℂ) + t * Complex.I) * y +
          ((3 / 4 : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2))‖) := by
  let B : ℝ → ℝ := fun t => 32 * (1 + |t|) ^ 2 *
    ‖Complex.exp (((3 / 4 : ℂ) + t * Complex.I) * y +
      ((3 / 4 : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2))‖
  have hiB : Integrable B := pole_gaussian_polynomial_integrable hM y
  apply ((inverse_square_summable S hN).mul_left (∫ t, B t)).of_nonneg_of_le
  · intro j
    exact integral_nonneg (fun t => norm_nonneg _)
  · intro j
    rw [← integral_mul_const]
    apply integral_mono (pole_gaussian_integrable S j hM y).norm
      (hiB.mul_const ((S.mult j : ℝ) / S.gamma j ^ 2))
    intro t
    dsimp only
    rw [norm_mul]
    simpa only [B, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right (pole_vertical_bound S j t)
        (norm_nonneg (Complex.exp (((3 / 4 : ℂ) + t * Complex.I) * y +
          ((3 / 4 : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2))))

/-- Increasing ordinate cutoffs exhaust the spectrum as finite subsets. -/
theorem spectrum_cut_tendsto (S : Spectrum) : Tendsto S.cut atTop atTop := by
  classical
  apply Monotone.tendsto_atTop_finset
  · intro u v huv j hj
    simp only [Spectrum.cut, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hj ⊢
    exact hj.trans huv
  · intro j
    exact ⟨S.gamma j, by simp [Spectrum.cut]⟩

/-- Integrals of finite paired-pole cutoffs converge to the Gaussian integral of the full series. -/
theorem pole_gaussian_cutoff_tendsto (S : Spectrum) (hN : CountAsymptotic S)
    {M : ℝ} (hM : 0 < M) (y : ℝ) :
    Tendsto (fun T : ℝ => ∫ t : ℝ,
      (∑ j ∈ S.cut T, poleTerm S j ((3 / 4 : ℂ) + t * Complex.I)) *
        Complex.exp (((3 / 4 : ℂ) + t * Complex.I) * y +
          ((3 / 4 : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2))) atTop
      (𝓝 (∫ t : ℝ, (∑' j : S.index, poleTerm S j ((3 / 4 : ℂ) + t * Complex.I)) *
        Complex.exp (((3 / 4 : ℂ) + t * Complex.I) * y +
          ((3 / 4 : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2)))) := by
  classical
  have : Countable S.index := spectrum_countable S
  have h := hasSum_integral_of_summable_integral_norm
    (fun j => pole_gaussian_integrable S j hM y)
    (pole_gaussian_integral_norm_summable S hN hM y)
  have hh := h.comp (spectrum_cut_tendsto S)
  simpa only [Function.comp_def, Finset.sum_mul, integral_finsetSum _ (fun j _ =>
    pole_gaussian_integrable S j hM y), tsum_mul_right] using hh

end
end D5.S3.Analytic.Laplace.GaussianBoundary
