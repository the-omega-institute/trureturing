/- GID: D5/S3/Analytic/Oscillation/GaussianWindowLower
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/GaussianWindowLower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A bounded smooth multiplier transfers hard spectral window mass to Gaussian weights. -/

import D5.S3.Analytic.Oscillation.GaussianSpectrum
import D5.S3.Analytic.Oscillation.MontgomeryWindow
import D5.S3.Analytic.Fourier.GaussianCutoff
import D5.S3.Analytic.Fourier.ConvolutionL2
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace D5.S3.Analytic.Oscillation.GaussianWindowLower

open D5.S3.Analytic.Oscillation.OrdinateCounting
open D5.S3.Analytic.Oscillation.GaussianSpectrum
open D5.S3.Analytic.Oscillation.MontgomeryWindow
open D5.S3.Analytic.Fourier.GaussianCutoff
open D5.S3.Analytic.Fourier.ConvolutionL2
open Set Filter MeasureTheory
open scoped Topology BigOperators FourierTransform

noncomputable section

private def smoothCos (S : Spectrum) (M y : ℝ) : ℝ :=
  ∑ j ∈ S.cut (M + cutoffWidth M),
    (S.mult j : ℝ) * χ M (S.gamma j) * Real.cos (S.gamma j * y)

private lemma kernel_mul_integrable (M : ℝ) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f volume) {B : ℝ} (hB : ∀ v, ‖f v‖ ≤ B) :
    Integrable (fun v => cutoffKernel M v * f v) :=
  (cutoff_kernel_integrable M).mul_bdd hf (ae_of_all _ hB)

private lemma kernel_gaussian_integrable (S : Spectrum) (hN : CountAsymptotic S)
    {M : ℝ} (hM : 0 < M) (y : ℝ) :
    Integrable (fun v => cutoffKernel M v * gaussianCos S M (y - v)) := by
  apply kernel_mul_integrable M
    (((gaussianCos_continuous S hN hM).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable)
  intro v
  exact abs_gaussianCos_le S hN hM _

private lemma cutoff_convolution (S : Spectrum) (hN : CountAsymptotic S)
    {M : ℝ} (hM : 1 ≤ M) (y : ℝ) :
    (∫ v, cutoffKernel M v * gaussianCos S M (y - v)) = smoothCos S M y := by
  classical
  have := spectrum_countable S
  have hMp : 0 < M := by linarith
  let a : S.index → ℝ := fun j =>
    (S.mult j : ℝ) * Real.exp (-S.gamma j ^ 2 / (2 * M ^ 2))
  let F : S.index → ℝ → ℝ := fun j v =>
    cutoffKernel M v * (a j * Real.cos (S.gamma j * (y - v)))
  have ha : Summable a := gaussian_coefficients_summable S hN hMp
  have hF (j : S.index) : Integrable (F j) := by
    apply kernel_mul_integrable M (by dsimp [a]; fun_prop)
    intro v
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by dsimp [a]; positivity)]
    exact mul_le_of_le_one_right (by dsimp [a]; positivity) (Real.abs_cos_le_one _)
  have hdom (j : S.index) (v : ℝ) : ‖F j v‖ ≤ ‖cutoffKernel M v‖ * a j := by
    change |cutoffKernel M v * (a j * Real.cos (S.gamma j * (y - v)))| ≤
      |cutoffKernel M v| * a j
    rw [abs_mul, abs_mul,
      abs_of_nonneg (show 0 ≤ a j by dsimp [a]; positivity)]
    rw [← mul_assoc]
    exact mul_le_of_le_one_right (by positivity)
      (by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (S.gamma j * (y - v)))
  have hsum : Summable (fun j => ∫ v, ‖F j v‖) := by
    apply (ha.mul_left (∫ v, ‖cutoffKernel M v‖)).of_nonneg_of_le
    · intro j; exact integral_nonneg (fun v => norm_nonneg _)
    · intro j
      simpa only [integral_mul_const] using
        integral_mono (hF j).norm ((cutoff_kernel_integrable M).norm.mul_const (a j)) (hdom j)
  have hpoint (v : ℝ) : (∑' j, F j v) = cutoffKernel M v * gaussianCos S M (y - v) := by
    exact tsum_mul_left
  rw [← show (fun v => ∑' j, F j v) =
    (fun v => cutoffKernel M v * gaussianCos S M (y - v)) from funext hpoint,
    ← integral_tsum_of_summable_integral_norm hF hsum]
  have heach (j : S.index) : (∫ v, F j v) =
      (S.mult j : ℝ) * χ M (S.gamma j) * Real.cos (S.gamma j * y) := by
    have he : F j = fun v => a j *
        (cutoffKernel M v * Real.cos (S.gamma j * (y - v))) := by ext v; dsimp [F]; ring
    rw [he, integral_const_mul, cutoff_kernel_cos hM]
    dsimp [a]
    have hex : Real.exp (-S.gamma j ^ 2 / (2 * M ^ 2)) *
        Real.exp (S.gamma j ^ 2 / (2 * M ^ 2)) = 1 := by
      rw [← Real.exp_add]
      rw [show -S.gamma j ^ 2 / (2 * M ^ 2) + S.gamma j ^ 2 / (2 * M ^ 2) = 0 by ring,
        Real.exp_zero]
    calc
      _ = (S.mult j : ℝ) *
          (Real.exp (-S.gamma j ^ 2 / (2 * M ^ 2)) *
            Real.exp (S.gamma j ^ 2 / (2 * M ^ 2))) *
          χ M (S.gamma j) * Real.cos (S.gamma j * y) := by ring
      _ = _ := by rw [hex]; ring
  simp_rw [heach]
  apply tsum_eq_sum
  intro j hj
  have hj' : M + cutoffWidth M ≤ |S.gamma j| := by
    rw [abs_of_pos (S.gamma_pos j)]
    exact le_of_lt (lt_of_not_ge (by simpa [Spectrum.cut] using hj))
  rw [chi_eq_zero hMp hj']
  ring

private lemma smooth_hard_difference (S : Spectrum) {M : ℝ} (hM : 1 ≤ M) (y : ℝ) :
    |smoothCos S M y - hardCos S M y| ≤
      (S.N (M + cutoffWidth M) : ℝ) - (S.N M : ℝ) := by
  classical
  have hd : 0 < cutoffWidth M := Real.rpow_pos_of_pos (by linarith) _
  have hsub : S.cut M ⊆ S.cut (M + cutoffWidth M) := by
    intro j hj
    have hj' : S.gamma j ≤ M := by simpa [Spectrum.cut] using hj
    simpa [Spectrum.cut] using (show S.gamma j ≤ M + cutoffWidth M by linarith)
  have hone : (∑ j ∈ S.cut M,
      (S.mult j : ℝ) * χ M (S.gamma j) * Real.cos (S.gamma j * y)) = hardCos S M y := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : |S.gamma j| ≤ M := by
      rw [abs_of_pos (S.gamma_pos j)]
      simpa [Spectrum.cut] using hj
    rw [chi_eq_one (by linarith) hj', mul_one]
  have hdiff := Finset.sum_sdiff hsub
    (f := fun j => (S.mult j : ℝ) * χ M (S.gamma j) * Real.cos (S.gamma j * y))
  rw [hone] at hdiff
  have hc := Finset.sum_sdiff hsub (f := fun j => (S.mult j : ℝ))
  rw [show smoothCos S M y - hardCos S M y =
      ∑ j ∈ S.cut (M + cutoffWidth M) \ S.cut M,
        (S.mult j : ℝ) * χ M (S.gamma j) * Real.cos (S.gamma j * y) by
    dsimp [smoothCos] at *; linarith [hdiff]]
  calc
    _ ≤ ∑ j ∈ S.cut (M + cutoffWidth M) \ S.cut M,
        |(S.mult j : ℝ) * χ M (S.gamma j) * Real.cos (S.gamma j * y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ S.cut (M + cutoffWidth M) \ S.cut M, (S.mult j : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (chi_nonneg M _))]
      exact (mul_le_of_le_one_right (by positivity [chi_nonneg M (S.gamma j)])
        (Real.abs_cos_le_one _)).trans
        (mul_le_of_le_one_right (Nat.cast_nonneg _) (chi_le_one M _))
    _ = _ := by simp only [Spectrum.N, Nat.cast_sum] at *; linarith [hc]

private def clippedGaussian (S : Spectrum) (M : ℝ) : ℝ → ℝ :=
  (Icc (16 * Real.log M - 1) (20 * Real.log M + 1)).indicator (gaussianCos S M)

private def localizedCos (S : Spectrum) (M y : ℝ) : ℝ :=
  ∫ v, cutoffKernel M v * clippedGaussian S M (y - v)

private lemma clipped_measurable (S : Spectrum) (hN : CountAsymptotic S)
    {M : ℝ} (hM : 0 < M) : Measurable (clippedGaussian S M) :=
  (gaussianCos_continuous S hN hM).measurable.indicator measurableSet_Icc

private lemma gaussianMass_nonneg (S : Spectrum) (M : ℝ) : 0 ≤ gaussianMass S M :=
  tsum_nonneg (fun j => by positivity)

private lemma clipped_bound (S : Spectrum) (hN : CountAsymptotic S)
    {M : ℝ} (hM : 0 < M) (y : ℝ) :
    |clippedGaussian S M y| ≤ gaussianMass S M := by
  unfold clippedGaussian
  by_cases hy : y ∈ Icc (16 * Real.log M - 1) (20 * Real.log M + 1)
  · rw [indicator_of_mem hy]; exact abs_gaussianCos_le S hN hM y
  · rw [indicator_of_notMem hy, abs_zero]; exact gaussianMass_nonneg S M

private lemma localization_error (S : Spectrum) (hN : CountAsymptotic S)
    {M : ℝ} (hM : 0 < M) {y : ℝ}
    (hy : y ∈ Icc (16 * Real.log M) (20 * Real.log M)) :
    |localizedCos S M y - (∫ v, cutoffKernel M v * gaussianCos S M (y - v))| ≤
      (∫ v in {v : ℝ | 1 ≤ |v|}, ‖cutoffKernel M v‖) * gaussianMass S M := by
  classical
  let T : Set ℝ := {v | 1 ≤ |v|}
  have hT : MeasurableSet T := isClosed_le continuous_const continuous_abs |>.measurableSet
  have hg : Integrable (fun v => cutoffKernel M v * clippedGaussian S M (y - v)) :=
    kernel_mul_integrable M
      (((clipped_measurable S hN hM).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable)
      (fun v => clipped_bound S hN hM _)
  have hG := kernel_gaussian_integrable S hN hM y
  have he : localizedCos S M y - (∫ v, cutoffKernel M v * gaussianCos S M (y - v)) =
      ∫ v, cutoffKernel M v * (clippedGaussian S M (y - v) - gaussianCos S M (y - v)) := by
    rw [localizedCos, ← integral_sub hg hG]
    congr 1; ext v; ring
  rw [he]
  have hbound (v : ℝ) :
      ‖cutoffKernel M v * (clippedGaussian S M (y - v) - gaussianCos S M (y - v))‖ ≤
        T.indicator (fun v => ‖cutoffKernel M v‖) v * gaussianMass S M := by
    by_cases hv : v ∈ T
    · rw [indicator_of_mem hv, norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      by_cases hi : y - v ∈ Icc (16 * Real.log M - 1) (20 * Real.log M + 1)
      · simp [clippedGaussian, indicator_of_mem hi, gaussianMass_nonneg S M]
      · simpa [clippedGaussian, indicator_of_notMem hi] using abs_gaussianCos_le S hN hM (y - v)
    · have hv' : |v| < 1 := lt_of_not_ge hv
      have hi : y - v ∈ Icc (16 * Real.log M - 1) (20 * Real.log M + 1) :=
        ⟨by linarith [hy.1, (abs_lt.mp hv').2], by linarith [hy.2, (abs_lt.mp hv').1]⟩
      simp [clippedGaussian, indicator_of_mem hi, indicator_of_notMem hv]
  calc
    _ ≤ ∫ v, ‖cutoffKernel M v *
        (clippedGaussian S M (y - v) - gaussianCos S M (y - v))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ v, T.indicator (fun v => ‖cutoffKernel M v‖) v * gaussianMass S M := by
      apply integral_mono
      · simpa only [mul_sub, Pi.sub_apply] using (hg.sub hG).norm
      · exact ((cutoff_kernel_integrable M).norm.indicator hT).mul_const _
      · exact hbound
    _ = _ := by rw [integral_mul_const, integral_indicator hT]

private lemma total_error (S : Spectrum) (hN : CountAsymptotic S) (hlocal : LocalCount S) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 1 ≤ M →
      ∀ y ∈ Icc (16 * Real.log M) (20 * Real.log M),
        |localizedCos S M y - hardCos S M y| ≤
          C * cutoffWidth M * Real.log (2 + M) := by
  obtain ⟨A, hA, ht⟩ := transition_mass_bound S hlocal
  obtain ⟨B, hB, hg⟩ := gaussian_mass_bound S hN
  obtain ⟨K, hK, hk⟩ := cutoff_kernel_tail
  refine ⟨A + K * B, by positivity, fun M hM y hy => ?_⟩
  have hMp : 0 < M := by linarith
  have hd : 1 ≤ cutoffWidth M := Real.one_le_rpow hM (by norm_num)
  have hdM : cutoffWidth M ≤ M := by
    simpa [cutoffWidth] using Real.rpow_le_rpow_of_exponent_le hM
      (show (1 / 4 : ℝ) ≤ 1 by norm_num)
  have hl : 0 ≤ Real.log (2 + M) := Real.log_nonneg (by linarith)
  have hloc := localization_error S hN hMp hy
  have hmass := gaussianMass_nonneg S M
  have hb := mul_le_mul (hk M hM) (hg M hM) hmass (by positivity : 0 ≤ K / M)
  have heq : K / M * (B * M * Real.log (2 + M)) = K * B * Real.log (2 + M) := by
    field_simp
  rw [heq] at hb
  rw [cutoff_convolution S hN hM] at hloc
  simp only [Real.norm_eq_abs] at hloc
  have hs := (smooth_hard_difference S hM y).trans (ht M (cutoffWidth M) hM hd hdM)
  have htri := abs_sub_le (localizedCos S M y) (smoothCos S M y) (hardCos S M y)
  have hwidth := mul_le_mul_of_nonneg_right hd (show 0 ≤ K * B * Real.log (2 + M) by positivity)
  nlinarith

private lemma clipped_square_integrable (S : Spectrum) (hN : CountAsymptotic S)
    {M : ℝ} (hM : 0 < M) : Integrable (fun y => clippedGaussian S M y ^ 2) := by
  have hi : IntegrableOn (fun y => gaussianCos S M y ^ 2)
      (Icc (16 * Real.log M - 1) (20 * Real.log M + 1)) :=
    ((gaussianCos_continuous S hN hM).pow 2).integrableOn_Icc
  convert hi.integrable_indicator measurableSet_Icc using 1
  ext y
  simp only [clippedGaussian, indicator_apply]
  split_ifs <;> simp

private lemma localized_square_bound (S : Spectrum) (hN : CountAsymptotic S)
    {M : ℝ} (hM : 1 ≤ M) :
    Integrable (fun y => localizedCos S M y ^ 2) ∧
      (∫ y, localizedCos S M y ^ 2) ≤
        (Real.exp 2) ^ 2 *
          ∫ y in Icc (16 * Real.log M - 1) (20 * Real.log M + 1), gaussianCos S M y ^ 2 := by
  have hf := clipped_square_integrable S hN (by linarith : 0 < M)
  have hb : ∀ ξ : ℝ, ‖𝓕 (cutoffKernelSchwartz M) ξ‖ ≤ Real.exp 2 := by
    intro ξ
    simpa only [SchwartzMap.fourier_coe,
      show (cutoffKernelSchwartz M : ℝ → ℂ) = (fun v => (cutoffKernel M v : ℂ)) from
        funext (cutoff_kernelSchwartz_coe M)] using cutoff_multiplier_bound hM ξ
  have h := real_schwartz_convolution_l2_multiplier_of_complex (cutoffKernelSchwartz M)
    (cutoff_kernelSchwartz_coe M)
    (clipped_measurable S hN (by linarith : 0 < M)).aestronglyMeasurable hf
    (Real.exp_pos 2).le hb
  have he : (∫ y, clippedGaussian S M y ^ 2) =
      ∫ y in Icc (16 * Real.log M - 1) (20 * Real.log M + 1), gaussianCos S M y ^ 2 := by
    rw [← integral_indicator measurableSet_Icc]
    congr 1; ext y
    simp only [clippedGaussian, indicator_apply]
    split_ifs <;> simp
  rw [he] at h
  exact h

private lemma hard_square_integral_le (S : Spectrum) (hN : CountAsymptotic S)
    {M C : ℝ} (hM : 1 ≤ M) (hC : 0 ≤ C)
    (herr : ∀ y ∈ Icc (16 * Real.log M) (20 * Real.log M),
      |localizedCos S M y - hardCos S M y| ≤ C) :
    (∫ y in (16 * Real.log M)..(20 * Real.log M), hardCos S M y ^ 2) ≤
      2 * (Real.exp 2) ^ 2 *
        (∫ y in (16 * Real.log M - 1)..(20 * Real.log M + 1), gaussianCos S M y ^ 2) +
      8 * Real.log M * C ^ 2 := by
  have hL : 0 ≤ Real.log M := Real.log_nonneg hM
  have hab : 16 * Real.log M ≤ 20 * Real.log M := by nlinarith
  have hab' : 16 * Real.log M - 1 ≤ 20 * Real.log M + 1 := by nlinarith
  have hhard := hardCos_continuous S M
  obtain ⟨hi, hb⟩ := localized_square_bound S hN hM
  have hpoint (y : ℝ) (hy : y ∈ Icc (16 * Real.log M) (20 * Real.log M)) :
      hardCos S M y ^ 2 ≤ 2 * localizedCos S M y ^ 2 + 2 * C ^ 2 := by
    have he := (sq_le_sq₀ (abs_nonneg _) hC).mpr (herr y hy)
    rw [sq_abs] at he
    nlinarith [sq_nonneg (hardCos S M y - 2 * localizedCos S M y)]
  have hm := setIntegral_mono_on (hhard.pow 2).integrableOn_Icc
    ((hi.integrableOn.const_mul 2).add (integrableOn_const (C := 2 * C ^ 2) (by simp)))
    measurableSet_Icc hpoint
  simp only [Pi.add_apply, Pi.pow_apply] at hm
  rw [integral_add (hi.integrableOn.const_mul 2) (integrableOn_const (by simp)),
    integral_const_mul, setIntegral_const, Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ 20 * Real.log M - 16 * Real.log M),
    smul_eq_mul] at hm
  have hsub := setIntegral_le_integral (s := Icc (16 * Real.log M) (20 * Real.log M)) hi
    (ae_of_all _ (fun y => sq_nonneg (localizedCos S M y)))
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab', ← integral_Icc_eq_integral_Ioc]
  nlinarith

private lemma error_small {a C : ℝ} (ha : 0 < a) :
    ∀ᶠ M : ℝ in atTop, 1 ≤ M ∧
      8 * Real.log M * (C * cutoffWidth M * Real.log (2 + M)) ^ 2 ≤
        a / 2 * M * (Real.log M) ^ 2 := by
  have ht := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero
  have he := (ht.const_mul (32 * C ^ 2)).eventually
    (gt_mem_nhds (show (32 * C ^ 2) * 0 < a / 2 by linarith))
  filter_upwards [he, eventually_ge_atTop (2 : ℝ)] with M he hM
  have hMp : 0 < M := by linarith
  have hL : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
  have hL' : 0 ≤ Real.log (2 + M) := Real.log_nonneg (by linarith)
  have hlog : Real.log (2 + M) ≤ 2 * Real.log M := by
    calc
      _ ≤ Real.log (M ^ 2) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; norm_num
  have hd : cutoffWidth M ^ 2 = M ^ (1 / 2 : ℝ) := by
    rw [cutoffWidth, ← Real.rpow_mul_natCast hMp.le]
    norm_num
  have hs : M ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ) = M := by
    rw [← Real.rpow_add hMp]; norm_num
  have hhalf : 0 < M ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hMp _
  have he' : 32 * C ^ 2 * Real.log M ≤ a / 2 * M ^ (1 / 2 : ℝ) :=
    (div_le_iff₀ hhalf).mp (by simpa only [mul_div_assoc] using he.le)
  have he'' := mul_le_mul_of_nonneg_right he'
    (show 0 ≤ M ^ (1 / 2 : ℝ) * (Real.log M) ^ 2 by positivity)
  have hlog2 := (sq_le_sq₀ hL' (by positivity : 0 ≤ 2 * Real.log M)).mpr hlog
  have hfirst := mul_le_mul_of_nonneg_left hlog2
    (show 0 ≤ 8 * Real.log M * C ^ 2 * cutoffWidth M ^ 2 by positivity)
  refine ⟨by linarith, ?_⟩
  calc
    _ ≤ 32 * C ^ 2 * (M ^ (1 / 2 : ℝ) * (Real.log M) ^ 3) := by
      rw [← hd]
      nlinarith only [hfirst]
    _ = (32 * C ^ 2 * Real.log M) * (M ^ (1 / 2 : ℝ) * (Real.log M) ^ 2) := by ring
    _ ≤ (a / 2 * M ^ (1 / 2 : ℝ)) * (M ^ (1 / 2 : ℝ) * (Real.log M) ^ 2) := he''
    _ = a / 2 * (M ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ)) * (Real.log M) ^ 2 := by ring
    _ = _ := by rw [hs]

/-- Local counting and averaged Montgomery positivity force Gaussian mass on the enlarged window. -/
theorem gaussian_window_lower (S : Spectrum) (hN : CountAsymptotic S)
    (hlocal : LocalCount S) (hMont : AveragedMontgomeryLower S) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ M : ℝ in atTop,
      c * M * (Real.log M) ^ 2 ≤
        ∫ y in (16 * Real.log M - 1)..(20 * Real.log M + 1), gaussianCos S M y ^ 2 := by
  obtain ⟨a, ha, hhard⟩ := hard_window_lower S hN hMont
  obtain ⟨C, hC, herr⟩ := total_error S hN hlocal
  refine ⟨a / (4 * (Real.exp 2) ^ 2), by positivity, ?_⟩
  filter_upwards [hhard, error_small (C := C) ha] with M hhard hsmall
  have he := hard_square_integral_le S hN hsmall.1
    (show 0 ≤ C * cutoffWidth M * Real.log (2 + M) by
      exact mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _))
        (Real.log_nonneg (by linarith))) (herr M hsmall.1)
  have hp : 0 < (Real.exp 2) ^ 2 := by positivity
  have hh : a / 2 * M * (Real.log M) ^ 2 ≤
      2 * (Real.exp 2) ^ 2 *
        ∫ y in (16 * Real.log M - 1)..(20 * Real.log M + 1), gaussianCos S M y ^ 2 := by
    linarith [hsmall.2]
  apply (le_of_mul_le_mul_left (a := 4 * (Real.exp 2) ^ 2) ?_ (by positivity))
  calc
    _ = 2 * (a / 2 * M * (Real.log M) ^ 2) := by field_simp
    _ ≤ _ := by nlinarith only [hh]

end
end D5.S3.Analytic.Oscillation.GaussianWindowLower
