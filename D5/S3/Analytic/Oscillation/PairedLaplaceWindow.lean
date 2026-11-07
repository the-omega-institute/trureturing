/- GID: D5/S3/Analytic/Oscillation/PairedLaplaceWindow
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/PairedLaplaceWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian localization transfers spectral window mass to paired Laplace data. -/

import D5.S3.Analytic.Laplace.GaussianBoundary
import D5.S3.Analytic.Oscillation.GaussianWindowLower
import D5.S3.Analytic.Fourier.ConvolutionL2

/-! Square mass of paired Laplace data on logarithmic windows. -/

namespace D5.S3.Analytic.Oscillation.PairedLaplaceWindow

open D5.S3.Analytic.Oscillation.OrdinateCounting
open D5.S3.Analytic.Oscillation.GaussianSpectrum
open D5.S3.Analytic.Oscillation.MontgomeryWindow
open D5.S3.Analytic.Oscillation.GaussianWindowLower
open D5.S3.Analytic.Laplace.PairedPoleRegularity
open D5.S3.Analytic.Laplace.GaussianBoundary
open D5.S3.Analytic.Fourier.GaussianKernel
open D5.S3.Analytic.Fourier.ConvolutionL2
open MeasureTheory Set Filter
open scoped Topology

noncomputable section

private lemma tail_exponent {M v : ℝ} (hM : 1 ≤ M) (hv : 1 ≤ |v|) :
    -M ^ 2 * v ^ 2 / 2 ≤ 3 * v / 4 + 1 - M ^ 2 / 8 := by
  have hM2 : 1 ≤ M ^ 2 := by nlinarith
  have hv2 : 1 ≤ v ^ 2 := by nlinarith [sq_abs v]
  have hp1 : M ^ 2 ≤ M ^ 2 * v ^ 2 := by nlinarith
  have hp2 : v ^ 2 ≤ M ^ 2 * v ^ 2 := by nlinarith
  nlinarith [sq_nonneg (v + 1)]

private lemma tail_gaussian_weight {M y u : ℝ} (hM : 1 ≤ M) (hu : 1 ≤ |y - u|) :
    q M (y - u) ≤ M / Real.sqrt (2 * Real.pi) *
      Real.exp (3 * y / 4 + 1) * Real.exp (-M ^ 2 / 8) * Real.exp (-3 * u / 4) := by
  have he := tail_exponent hM hu
  unfold q
  have hr : 3 * (y - u) / 4 + 1 - M ^ 2 / 8 =
      (3 * y / 4 + 1) + (-M ^ 2 / 8) + (-3 * u / 4) := by ring
  rw [hr] at he
  simpa only [Real.exp_add, mul_assoc] using
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
      (show 0 ≤ M / Real.sqrt (2 * Real.pi) by positivity)

private lemma tail_distance {a b y u : ℝ} (hy : y ∈ Icc (a + 1) (b - 1))
    (hu : u ∉ Icc a b) : 1 ≤ |y - u| := by
  simp only [mem_Icc, not_and_or, not_le] at hu
  rcases hu with hu | hu
  · rw [abs_of_nonneg (by linarith [hy.1] : 0 ≤ y - u)]; linarith [hy.1]
  · rw [abs_of_nonpos (by linarith [hy.2] : y - u ≤ 0)]; linarith [hy.2]

private lemma tail_uniform {M y u : ℝ} (hM : 1 ≤ M)
    (hy : y ≤ 20 * Real.log M + 1) (hu : 1 ≤ |y - u|) :
    q M (y - u) ≤
      (Real.exp (7 / 4) / Real.sqrt (2 * Real.pi) * M ^ 16 * Real.exp (-M / 8)) *
        Real.exp (-3 * u / 4) := by
  have hM0 : 0 < M := by linarith
  have he : Real.exp (3 * y / 4 + 1) ≤ Real.exp (7 / 4) * M ^ 15 := by
    calc
      _ ≤ Real.exp (15 * Real.log M + 7 / 4) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by
        rw [Real.exp_add]
        rw [show (15 : ℝ) * Real.log M = (15 : ℕ) * Real.log M by norm_num, Real.exp_nat_mul, Real.exp_log hM0]
        ring
  have hdecay : Real.exp (-M ^ 2 / 8) ≤ Real.exp (-M / 8) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h := tail_gaussian_weight hM hu
  have hp := mul_le_mul he hdecay (Real.exp_pos _).le (by positivity : 0 ≤ Real.exp (7 / 4) * M ^ 15)
  calc
    _ ≤ (M / Real.sqrt (2 * Real.pi)) *
        (Real.exp (3 * y / 4 + 1) * Real.exp (-M ^ 2 / 8)) * Real.exp (-3 * u / 4) := by nlinarith only [h]
    _ ≤ (M / Real.sqrt (2 * Real.pi)) *
        ((Real.exp (7 / 4) * M ^ 15) * Real.exp (-M / 8)) * Real.exp (-3 * u / 4) := by
      gcongr
    _ = _ := by ring

private lemma tail_eventually :
    ∀ᶠ M : ℝ in atTop, 1 ≤ M ∧
      ∀ y u : ℝ, y ≤ 20 * Real.log M + 1 → 1 ≤ |y - u| →
        q M (y - u) ≤ Real.exp (-3 * u / 4) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 16 (1 / 8) (by norm_num)).const_mul
    (Real.exp (7 / 4) / Real.sqrt (2 * Real.pi))
  have he := ht.eventually (gt_mem_nhds (show (Real.exp (7 / 4) / Real.sqrt (2 * Real.pi)) * 0 < 1 by simp))
  filter_upwards [eventually_ge_atTop (1 : ℝ), he] with M hM he
  refine ⟨hM, fun y u hy hu => ?_⟩
  have hb := tail_uniform hM hy hu
  have he' : Real.exp (7 / 4) / Real.sqrt (2 * Real.pi) * M ^ 16 * Real.exp (-M / 8) ≤ 1 := by
    simp only [Real.rpow_ofNat] at he
    simpa only [mul_assoc, show -(1 / 8 : ℝ) * M = -M / 8 by ring] using he.le
  exact hb.trans (by simpa using mul_le_mul_of_nonneg_right he' (Real.exp_pos (-3 * u / 4)).le)

private def clipped (f : ℝ → ℝ) (M : ℝ) : ℝ → ℝ :=
  (Icc (16 * Real.log M - 2) (20 * Real.log M + 2)).indicator f

private def localized (f : ℝ → ℝ) (M y : ℝ) : ℝ :=
  ∫ v, q M v * clipped f M (y - v)

private lemma clipped_measurable {S : Spectrum} {f : ℝ → ℝ}
    (D : PairedLaplaceData S f 2) (M : ℝ) : Measurable (clipped f M) :=
  D.measurable.indicator measurableSet_Icc

private lemma clipped_bound {S : Spectrum} {f : ℝ → ℝ}
    (D : PairedLaplaceData S f 2) {M : ℝ} (hM : 1 ≤ M)
    (hlower : 0 ≤ 16 * Real.log M - 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u, |clipped f M u| ≤ B := by
  have hL : 0 ≤ Real.log M := Real.log_nonneg hM
  obtain ⟨B, hB, hb⟩ := D.local_bound (20 * Real.log M + 2) (by positivity)
  refine ⟨B, hB, fun u => ?_⟩
  by_cases hu : u ∈ Icc (16 * Real.log M - 2) (20 * Real.log M + 2)
  · rw [clipped, indicator_of_mem hu]
    exact hb u ⟨le_trans hlower hu.1, hu.2⟩
  · simp [clipped, indicator_of_notMem hu, hB]

private lemma clipped_square_integrable {S : Spectrum} {f : ℝ → ℝ}
    (D : PairedLaplaceData S f 2) {M : ℝ} (hM : 1 ≤ M)
    (hlower : 0 ≤ 16 * Real.log M - 2) :
    Integrable (fun u => clipped f M u ^ 2) := by
  obtain ⟨B, hB, hb⟩ := clipped_bound D hM hlower
  have hi : IntegrableOn (fun u => f u ^ 2)
      (Icc (16 * Real.log M - 2) (20 * Real.log M + 2)) := by
    apply (integrableOn_const (C := B ^ 2) (by simp)).mono'
      (D.measurable.pow_const 2).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have h := hb u
    rw [clipped, indicator_of_mem hu] at h
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f u)), sq_abs] using
      (sq_le_sq₀ (abs_nonneg (f u)) hB).mpr h
  convert hi.integrable_indicator measurableSet_Icc using 1
  ext u
  simp only [clipped, indicator_apply]
  split_ifs <;> simp

private lemma localized_square_bound {S : Spectrum} {f : ℝ → ℝ}
    (D : PairedLaplaceData S f 2) {M : ℝ} (hM : 1 ≤ M)
    (hlower : 0 ≤ 16 * Real.log M - 2) :
    Integrable (fun y => localized f M y ^ 2) ∧
    (∫ y, localized f M y ^ 2) ≤
      ∫ y in (16 * Real.log M - 2)..(20 * Real.log M + 2), f y ^ 2 := by
  have hM0 : 0 < M := by linarith
  have hf := clipped_square_integrable D hM hlower
  have hm : AEStronglyMeasurable (clipped f M) volume :=
    (clipped_measurable D M).aestronglyMeasurable
  have hk : (∫ v, ‖q M v‖) = 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg ((q_laws hM0).2.1 _)]
      using (q_laws hM0).2.2
  have hb := real_convolution_l2_young (q_laws hM0).1 hm hf
    (show (0 : ℝ) ≤ 1 by norm_num) hk.le
  have hmem := (convolution_memLp_two (q_laws hM0).1.ofReal
    (((memLp_two_iff_integrable_sq hm).mpr hf).ofReal (K := ℂ))).1
  have hc (y : ℝ) :
      conv (fun v => (q M v : ℂ)) (fun u => (clipped f M u : ℂ)) y =
        (localized f M y : ℂ) := by
    simpa only [localized] using real_convolution_identity (q M) (clipped f M) y
  have hi : Integrable (fun y => localized f M y ^ 2) := by
    convert (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem using 1
    ext y
    have hn : ‖(localized f M y : ℂ)‖ ^ 2 = localized f M y ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact hn.symm.trans (congrArg (fun z : ℂ => ‖z‖ ^ 2) (hc y)).symm
  have he : (∫ y, clipped f M y ^ 2) =
      ∫ y in (16 * Real.log M - 2)..(20 * Real.log M + 2), f y ^ 2 := by
    rw [intervalIntegral.integral_of_le (by nlinarith [Real.log_nonneg hM]),
      ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
    congr 1
    ext y
    simp only [clipped, indicator_apply]
    split_ifs <;> simp
  refine ⟨hi, ?_⟩
  simpa only [one_pow, one_mul, ← he, localized] using hb

private lemma localized_integrable {S : Spectrum} {f : ℝ → ℝ}
    (D : PairedLaplaceData S f 2) {M : ℝ} (hM : 1 ≤ M)
    (hlower : 0 ≤ 16 * Real.log M - 2) (y : ℝ) :
    Integrable (fun u => clipped f M u * q M (y-u)) := by
  obtain ⟨B, hB, hb⟩ := clipped_bound D hM hlower
  exact ((q_laws (by linarith : 0 < M)).1.comp_sub_left y).bdd_mul
    (clipped_measurable D M).aestronglyMeasurable (ae_of_all _ hb)

private lemma localized_eq {f : ℝ → ℝ} (M y : ℝ) :
    localized f M y = ∫ u, clipped f M u * q M (y-u) := by
  rw [localized, ← integral_sub_left_eq_self (fun u => clipped f M u * q M (y-u)) volume y]
  congr 1
  ext v
  simp only [sub_sub_cancel]
  ring

private lemma boundary_window_bound {M C y : ℝ} (hM : 1 ≤ M)
    (hC : 0 ≤ C) (hy : 16 * Real.log M - 1 ≤ y) :
    C * M ^ 3 * Real.exp (-y / 6) ≤
      (C * Real.exp (1 / 6)) * M ^ (1 / 3 : ℝ) := by
  have hMp : 0 < M := by linarith
  calc
    _ ≤ C * M ^ 3 * Real.exp (-(16 * Real.log M - 1) / 6) := by
      gcongr
    _ = _ := by
      rw [Real.rpow_def_of_pos hMp]
      have hp : M ^ 3 = Real.exp (3 * Real.log M) := by
        rw [show (3 : ℝ) * Real.log M = (3 : ℕ) * Real.log M by norm_num,
          Real.exp_nat_mul, Real.exp_log hMp]
      rw [hp, mul_assoc C, ← Real.exp_add]
      rw [mul_assoc C, ← Real.exp_add]
      congr 2
      ring

private lemma squared_error_small {a C : ℝ} (ha : 0 < a) :
    ∀ᶠ M : ℝ in atTop, 1 ≤ Real.log M ∧
      (8 * Real.log M + 4) * (C * M ^ (1 / 3 : ℝ)) ^ 2 ≤
        a / 2 * M * (Real.log M) ^ 2 := by
  have ht := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 3 by norm_num)).const_mul
    (12 * C ^ 2)
  have he := ht.eventually (gt_mem_nhds (show 12 * C ^ 2 * 0 < a / 2 by linarith))
  filter_upwards [he, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop (1 : ℝ)] with M he hL hM
  have hMp : 0 < M := by linarith
  have hpower : (M ^ (1 / 3 : ℝ)) ^ 2 = M * M ^ (-(1 / 3 : ℝ)) := by
    calc
      _ = M ^ ((1 / 3 : ℝ) * 2) := (Real.rpow_mul_natCast hMp.le _ 2).symm
      _ = M ^ ((1 : ℝ) + -(1 / 3 : ℝ)) := by norm_num
      _ = _ := by rw [Real.rpow_add hMp, Real.rpow_one]
  have hmult := mul_le_mul_of_nonneg_right he.le
    (show 0 ≤ M * (Real.log M) ^ 2 by positivity)
  refine ⟨hL, ?_⟩
  calc
    _ ≤ 12 * (Real.log M) ^ 2 * (C * M ^ (1 / 3 : ℝ)) ^ 2 := by
      gcongr
      nlinarith [sq_nonneg (Real.log M - 1)]
    _ = (12 * C ^ 2 * M ^ (-(1 / 3 : ℝ))) * (M * (Real.log M) ^ 2) := by
      rw [mul_pow, hpower]; ring
    _ ≤ _ := by nlinarith only [hmult]

private lemma window_comparison (S : Spectrum) (hN : CountAsymptotic S)
    {M E : ℝ} {p : ℝ → ℝ} (hM : 1 ≤ M) (hE : 0 ≤ E)
    (hp : Integrable (fun y => p y ^ 2))
    (herr : ∀ y ∈ Icc (16 * Real.log M - 1) (20 * Real.log M + 1),
      |p y + gaussianCos S M y| ≤ E) :
    (∫ y in (16 * Real.log M - 1)..(20 * Real.log M + 1),
      gaussianCos S M y ^ 2) ≤
      2 * (∫ y, p y ^ 2) + (8 * Real.log M + 4) * E ^ 2 := by
  have hL : 0 ≤ Real.log M := Real.log_nonneg hM
  have hab : 16 * Real.log M - 1 ≤ 20 * Real.log M + 1 := by linarith
  have hg : IntegrableOn (fun y => gaussianCos S M y ^ 2)
      (Icc (16 * Real.log M - 1) (20 * Real.log M + 1)) :=
    ((gaussianCos_continuous S hN (by linarith : 0 < M)).pow 2).integrableOn_Icc
  have hpoint (y : ℝ) (hy : y ∈ Icc (16 * Real.log M - 1) (20 * Real.log M + 1)) :
      gaussianCos S M y ^ 2 ≤ 2 * p y ^ 2 + 2 * E ^ 2 := by
    have he := (sq_le_sq₀ (abs_nonneg _) hE).mpr (herr y hy)
    rw [sq_abs] at he
    nlinarith [sq_nonneg (gaussianCos S M y + 2 * p y)]
  have hm := setIntegral_mono_on hg
    ((hp.integrableOn.const_mul 2).add (integrableOn_const (C := 2 * E ^ 2) (by simp)))
    measurableSet_Icc hpoint
  simp only [Pi.add_apply] at hm
  rw [integral_add (hp.integrableOn.const_mul 2) (integrableOn_const (by simp)),
    integral_const_mul, setIntegral_const, Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith : 0 ≤
      (20 * Real.log M + 1) - (16 * Real.log M - 1)), smul_eq_mul] at hm
  have hsub := setIntegral_le_integral
    (s := Icc (16 * Real.log M - 1) (20 * Real.log M + 1)) hp
    (ae_of_all _ (fun y => sq_nonneg (p y)))
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  nlinarith

private lemma localization_error {S : Spectrum} {f : ℝ → ℝ}
    (D : PairedLaplaceData S f 2) {M y : ℝ} (hM : 1 ≤ M)
    (hlower : 0 ≤ 16 * Real.log M - 2)
    (hy : y ∈ Icc (16 * Real.log M - 1) (20 * Real.log M + 1))
    (hi : IntegrableOn (fun u => f u * q M (y - u)) (Ici 0))
    (htail : ∀ u : ℝ, 1 ≤ |y - u| → q M (y - u) ≤ Real.exp (-3 * u / 4)) :
    |gaussianAverage f M y - localized f M y| ≤
      ∫ u in Ici (0 : ℝ), |f u| * Real.exp (-3 * u / 4) := by
  have hM0 : 0 < M := by linarith
  have hiC := localized_integrable D hM hlower y
  have he : localized f M y = ∫ u in Ici (0 : ℝ), clipped f M u * q M (y - u) := by
    rw [localized_eq]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    have hu' : u ∉ Icc (16 * Real.log M - 2) (20 * Real.log M + 2) := by
      simp only [mem_Ici, not_le] at hu
      exact fun h => (not_lt_of_ge (hlower.trans h.1)) hu
    simp [clipped, indicator_of_notMem hu']
  rw [gaussianAverage, he, ← integral_sub hi hiC.integrableOn]
  have hpoint (u : ℝ) :
      ‖f u * q M (y-u) - clipped f M u * q M (y-u)‖ ≤
        |f u| * Real.exp (-3 * u / 4) := by
    by_cases hu : u ∈ Icc (16 * Real.log M - 2) (20 * Real.log M + 2)
    · simp only [clipped, indicator_of_mem hu, sub_self, norm_zero]
      positivity
    · have hd : 1 ≤ |y-u| := tail_distance
        (a := 16 * Real.log M - 2) (b := 20 * Real.log M + 2)
        ⟨by linarith [hy.1], by linarith [hy.2]⟩ hu
      simp only [clipped, indicator_of_notMem hu, zero_mul, sub_zero,
        Real.norm_eq_abs, abs_mul, abs_of_nonneg ((q_laws hM0).2.1 _)]
      exact mul_le_mul_of_nonneg_left (htail u hd) (abs_nonneg _)
  have hweight : IntegrableOn (fun u => |f u| * Real.exp (-3 * u / 4)) (Ici 0) := by
    apply (D.initial_convergence (3 / 4) (by norm_num)).norm.congr
    apply ae_of_all
    intro u
    dsimp only
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    congr 2
    ring
  calc
    _ ≤ ∫ u in Ici (0 : ℝ), ‖f u * q M (y-u) - clipped f M u * q M (y-u)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ _ := integral_mono (hi.sub hiC.integrableOn).norm hweight hpoint

/-- Averaged spectral positivity forces square mass of the original paired Laplace data. -/
theorem paired_laplace_window_lower
    (S : Spectrum) (hN : CountAsymptotic S)
    (hlocal : LocalCount S) (hMont : AveragedMontgomeryLower S)
    {f : ℝ → ℝ} (D : PairedLaplaceData S f 2)
    (hstrip : GaussianStripControl D.J) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ M : ℝ in Filter.atTop,
        c * M * (Real.log M) ^ 2 ≤
          ∫ y in (16 * Real.log M - 2)..(20 * Real.log M + 2), f y ^ 2 := by
  obtain ⟨a, ha, hG⟩ := gaussian_window_lower S hN hlocal hMont
  obtain ⟨B, hB, hboundary⟩ := gaussian_boundary S hN D hstrip
  let H : ℝ := ∫ u in Ici (0 : ℝ), |f u| * Real.exp (-3 * u / 4)
  have hH : 0 ≤ H := integral_nonneg (fun u => by positivity)
  let C : ℝ := B * Real.exp (1 / 6) + H
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨a / 4, by positivity, ?_⟩
  filter_upwards [hG, squared_error_small (C := C) ha, tail_eventually]
    with M hG hsmall htail
  have hM : 1 ≤ M := htail.1
  have hlower : 0 ≤ 16 * Real.log M - 2 := by linarith [hsmall.1]
  obtain ⟨hi, hyoung⟩ := localized_square_bound D hM hlower
  have herr (y : ℝ) (hy : y ∈ Icc (16 * Real.log M - 1) (20 * Real.log M + 1)) :
      |localized f M y + gaussianCos S M y| ≤ C * M ^ (1 / 3 : ℝ) := by
    have hy1 : 1 ≤ y := by linarith [hsmall.1, hy.1]
    have hb := hboundary M y hM hy1
    have hb' := hb.2.trans (boundary_window_bound hM hB.le hy.1)
    have ht := localization_error D hM hlower hy hb.1
      (fun u hu => htail.2 y u hy.2 hu)
    have hr : 1 ≤ M ^ (1 / 3 : ℝ) := Real.one_le_rpow hM (by norm_num)
    have hH' := mul_le_mul_of_nonneg_left hr hH
    calc
      _ = |(gaussianAverage f M y + gaussianCos S M y) -
          (gaussianAverage f M y - localized f M y)| := by congr 1; ring
      _ ≤ |gaussianAverage f M y + gaussianCos S M y| +
          |gaussianAverage f M y - localized f M y| := abs_sub _ _
      _ ≤ _ := by dsimp [C, H] at *; nlinarith
  have hc := window_comparison S hN hM
    (show 0 ≤ C * M ^ (1 / 3 : ℝ) by positivity) hi herr
  nlinarith [hsmall.2]

end
end D5.S3.Analytic.Oscillation.PairedLaplaceWindow
