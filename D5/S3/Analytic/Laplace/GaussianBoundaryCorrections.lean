/- GID: D5/S3/Analytic/Laplace/GaussianBoundaryCorrections
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/GaussianBoundaryCorrections
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian half-line corrections form an absolutely summable exponentially small spectral remainder. -/

import D5.S3.Analytic.Fourier.GaussianKernel
import D5.S3.Analytic.Oscillation.GaussianSpectrum

/-! The negative-half-line correction in Gaussian inversion of cosine poles. -/

namespace D5.S3.Analytic.Laplace.GaussianBoundary

open D5.S3.Analytic.Fourier.GaussianKernel
open D5.S3.Analytic.Oscillation.OrdinateCounting
open D5.S3.Analytic.Oscillation.GaussianSpectrum
open MeasureTheory Set Filter
open scoped Topology BigOperators

noncomputable section

noncomputable def gaussianCorrection (M y γ : ℝ) : ℝ :=
  ∫ v in Ici (0 : ℝ), Real.cos (γ * v) * q M (y + v)

/-- The Gaussian cosine transform on the positive ray differs from the full transform
by the reflected negative ray. -/
theorem gaussian_cos_halfline {M : ℝ} (hM : 0 < M) (γ y : ℝ) :
    (∫ u in Ici (0 : ℝ), Real.cos (γ * u) * q M (y - u)) =
      Real.exp (-γ ^ 2 / (2 * M ^ 2)) * Real.cos (γ * y) -
        gaussianCorrection M y γ := by
  have hi : Integrable (fun u => Real.cos (γ * u) * q M (y - u)) := by
    exact ((q_laws hM).1.comp_sub_left y).bdd_mul (by fun_prop)
      (ae_of_all _ (fun u => Real.abs_cos_le_one (γ * u)))
  have hn : (∫ u in Iic (0 : ℝ), Real.cos (γ * u) * q M (y - u)) =
      gaussianCorrection M y γ := by
    simpa only [gaussianCorrection, neg_zero, mul_neg, Real.cos_neg,
      sub_neg_eq_add, ← integral_Ici_eq_integral_Ioi] using
      (integral_comp_neg_Ioi (0 : ℝ)
        (fun u => Real.cos (γ * u) * q M (y - u))).symm
  have h := intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ))
    hi.integrableOn hi.integrableOn
  rw [hn, q_cos_convolution hM γ y, ← integral_Ici_eq_integral_Ioi] at h
  linarith

private lemma correction_term_bound (S : Spectrum) {M y : ℝ}
    (hM : 1 ≤ M) (hy : 1 ≤ y) (j : S.index) :
    ‖(S.mult j : ℝ) * gaussianCorrection M y (S.gamma j)‖ ≤
      (2 * M ^ 2 * y * q M y) * ((S.mult j : ℝ) / S.gamma j ^ 2) := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  have h := mul_le_mul_of_nonneg_left
    (gaussian_halfline_correction hM hy (S.gamma_pos j)) (Nat.cast_nonneg (S.mult j))
  simpa only [gaussianCorrection, Real.norm_eq_abs] using h.trans_eq (by ring)

/-- The multiplicity-weighted reflected Gaussian corrections are absolutely summable. -/
theorem gaussian_corrections_summable (S : Spectrum) (hN : CountAsymptotic S)
    {M y : ℝ} (hM : 1 ≤ M) (hy : 1 ≤ y) :
    Summable (fun j : S.index =>
      (S.mult j : ℝ) * gaussianCorrection M y (S.gamma j)) := by
  exact Summable.of_norm_bounded
    ((inverse_square_summable S hN).mul_left (2 * M ^ 2 * y * q M y))
    (correction_term_bound S hM hy)

private lemma gaussian_correction_scale {M y : ℝ} (hM : 1 ≤ M) (hy : 1 ≤ y) :
    M ^ 2 * y * q M y ≤
      (3 / Real.sqrt (2 * Real.pi)) * M ^ 3 * Real.exp (-y / 6) := by
  have hM0 : 0 < M := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hM2 : 1 ≤ M ^ 2 := by nlinarith
  have hy2 : y ≤ y ^ 2 := by nlinarith
  have hquad : y ≤ M ^ 2 * y ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hM2 (sq_nonneg y)]
  have he : y ≤ 3 * Real.exp (y / 3) := by
    linarith [Real.add_one_le_exp (y / 3)]
  have hdec : y * Real.exp (-M ^ 2 * y ^ 2 / 2) ≤ 3 * Real.exp (-y / 6) := by
    calc
      _ ≤ 3 * Real.exp (y / 3) * Real.exp (-M ^ 2 * y ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
      _ = 3 * Real.exp (y / 3 - M ^ 2 * y ^ 2 / 2) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        linarith
  have hs : 0 < Real.sqrt (2 * Real.pi) := by positivity
  calc
    _ = (M ^ 3 / Real.sqrt (2 * Real.pi)) *
        (y * Real.exp (-M ^ 2 * y ^ 2 / 2)) := by unfold q; ring
    _ ≤ (M ^ 3 / Real.sqrt (2 * Real.pi)) * (3 * Real.exp (-y / 6)) :=
      mul_le_mul_of_nonneg_left hdec (by positivity)
    _ = _ := by ring

/-- The sum of the reflected Gaussian corrections is bounded by a constant times
M cubed times exp(-y/6). -/
theorem gaussian_corrections_bound (S : Spectrum) (hN : CountAsymptotic S) :
    ∃ C : ℝ, 0 < C ∧ ∀ M y : ℝ, 1 ≤ M → 1 ≤ y →
      |∑' j : S.index, (S.mult j : ℝ) * gaussianCorrection M y (S.gamma j)| ≤
        C * M ^ 3 * Real.exp (-y / 6) := by
  let A : ℝ := ∑' j : S.index, (S.mult j : ℝ) / S.gamma j ^ 2
  have hA : 0 ≤ A := tsum_nonneg (fun j => by positivity)
  let C : ℝ := 6 / Real.sqrt (2 * Real.pi) * A + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun M y hM hy => ?_⟩
  have hs := gaussian_corrections_summable S hN hM hy
  calc
    _ ≤ ∑' j : S.index, ‖(S.mult j : ℝ) * gaussianCorrection M y (S.gamma j)‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' j : S.index,
        (2 * M ^ 2 * y * q M y) * ((S.mult j : ℝ) / S.gamma j ^ 2) :=
      hs.norm.tsum_le_tsum (correction_term_bound S hM hy)
        ((inverse_square_summable S hN).mul_left _)
    _ = (2 * M ^ 2 * y * q M y) * A := by rw [tsum_mul_left]
    _ ≤ (6 / Real.sqrt (2 * Real.pi) * A) * M ^ 3 * Real.exp (-y / 6) := by
      have h := mul_le_mul_of_nonneg_right (gaussian_correction_scale hM hy) (show 0 ≤ 2 * A by positivity)
      convert h using 1 <;> ring
    _ ≤ _ := by
      have hnon : 0 ≤ M ^ 3 * Real.exp (-y / 6) := by positivity
      dsimp [C]
      nlinarith

/-- The positive-ray Gaussian cosine integrals are summable with multiplicity. -/
theorem gaussian_halfline_summable (S : Spectrum) (hN : CountAsymptotic S)
    {M y : ℝ} (hM : 1 ≤ M) (hy : 1 ≤ y) :
    Summable (fun j : S.index => (S.mult j : ℝ) *
      ∫ u in Ici (0 : ℝ), Real.cos (S.gamma j * u) * q M (y - u)) := by
  have hM0 : 0 < M := by linarith
  convert (gaussianCos_summable S hN hM0 y).sub
    (gaussian_corrections_summable S hN hM hy) using 1
  ext j
  rw [gaussian_cos_halfline hM0]
  ring

end
end D5.S3.Analytic.Laplace.GaussianBoundary
