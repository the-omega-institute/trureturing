/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/SignedGaussianEndpoint
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/SignedGaussianEndpoint
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: A bounded correction and strict weighted Gaussian mass gap select a signed endpoint. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.SpectralAverage
import Mathlib.Analysis.Real.Pi.Bounds

/-! The Gaussian, complete spectrum, resolvent and spectral average are owned by
GaussianWindow, CountableResolvent and SpectralAverage. Only the bounded
correction and mean-to-point step are added here. All estimates are uniform
analytic families, with no finite computation or unpaid numerical premise. -/

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory MeasureTheory.Measure Filter
open scoped BigOperators Topology

namespace D5.S3.Weil.Mertens.IntegratedExplicit.SignedGaussianEndpoint

open D5.S3.Weil.Mertens.IntegratedExplicit.GaussianWindow
open D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent
open D5.S3.Weil.Mertens.IntegratedExplicit.SpectralAverage

private lemma exp_neg_sq_le_quarter {H : ℝ} (hH : 2 ≤ H) : exp (-H ^ 2) ≤ 1 / 4 := by
  rw [exp_neg, ← one_div]
  apply one_div_le_one_div_of_le (by norm_num)
  nlinarith [Real.add_one_le_exp (H ^ 2)]

private theorem window_mass {H : ℝ} (hH : 20000 ≤ H) :
    (1 / 2 : ℝ) ≤ ∫ _y in Icc H (4 * (H + 20) ^ 2), (1 : ℝ) ∂gaussian (H + 20) := by
  let w := H + 20
  have hHU : H ≤ 4 * w ^ 2 := by dsimp [w]; nlinarith [sq_nonneg H]
  have hs := integral_three_intervals (μ := gaussian w)
    (f := fun _ : ℝ => (1 : ℝ)) (integrable_const 1) hHU
  have hl := lower_tail H w 0 (by linarith) (by norm_num) (by norm_num)
  have hu := upper_tail w 0 (by norm_num)
  simp only [neg_zero, zero_mul, exp_zero] at hl hu
  have he1 : exp (2 * H - 3 * w ^ 2) ≤ exp (-H ^ 2) := by
    apply exp_le_exp.mpr
    dsimp [w]
    nlinarith [sq_nonneg H]
  have he2 : exp (-4 * w ^ 2) ≤ exp (-H ^ 2) := by
    apply exp_le_exp.mpr
    dsimp [w]
    nlinarith [sq_nonneg H]
  have he3 := exp_neg_sq_le_quarter (show 2 ≤ H by linarith)
  have hone : (∫ _y : ℝ, (1 : ℝ) ∂gaussian w) = 1 := by simp
  rw [hone] at hs
  change (1 / 2 : ℝ) ≤ ∫ _y in Icc H (4 * w ^ 2), (1 : ℝ) ∂gaussian w
  linarith

private lemma R_pos {y : ℝ} (hy : 0 < y) : 0 < R y := by unfold R; positivity

private lemma R_window_lower {H y : ℝ} (hH : 20000 ≤ H)
    (hy : y ∈ Icc H (4 * (H + 20) ^ 2)) : 1 / (4 * (H + 20) ^ 2) ≤ R y := by
  have hy0 : 0 < y := by linarith [hy.1]
  calc
    _ ≤ 1 / y := one_div_le_one_div_of_le hy0 hy.2
    _ ≤ R y := by
      dsimp [R]
      apply (div_le_div_iff₀ hy0 (sq_pos_of_pos hy0)).2
      nlinarith

private lemma R_window_integrable {H : ℝ} (hH : 20000 ≤ H) :
    IntegrableOn R (Icc H (4 * (H + 20) ^ 2)) (gaussian (H + 20)) := by
  have hc : ContinuousOn R (Icc H (4 * (H + 20) ^ 2)) := by
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    change ContinuousWithinAt (fun x : ℝ => (x + 1) / x ^ 2) _ y
    exact ((continuousAt_id.add_const 1).div (continuousAt_id.pow 2)
      (pow_ne_zero 2 hy0.ne')).continuousWithinAt
  exact hc.integrableOn_compact isCompact_Icc

private theorem weighted_window_mass {H : ℝ} (hH : 20000 ≤ H) :
    1 / (8 * (H + 20) ^ 2) ≤
      ∫ y in Icc H (4 * (H + 20) ^ 2), R y ∂gaussian (H + 20) := by
  let μ := gaussian (H + 20)
  let J := Icc H (4 * (H + 20) ^ 2)
  let c : ℝ := 1 / (4 * (H + 20) ^ 2)
  have hi : IntegrableOn (fun _ : ℝ => c) J μ := integrable_const c
  have hm := setIntegral_mono_on hi (R_window_integrable hH) measurableSet_Icc
    (fun y hy => R_window_lower hH hy)
  have he : (∫ _y in J, c ∂μ) = c * ∫ _y in J, (1 : ℝ) ∂μ := by
    rw [← integral_const_mul]
    simp
  rw [he] at hm
  have hmul := mul_le_mul_of_nonneg_left (window_mass hH) (show 0 ≤ c by positivity)
  calc
    _ = c * (1 / 2) := by
      dsimp [c]
      field_simp [show H + 20 ≠ 0 by linarith]
      <;> ring
    _ ≤ c * ∫ _y in J, (1 : ℝ) ∂μ := hmul
    _ ≤ _ := hm

private lemma square_cutoff {H : ℝ} (hH : 20000 ≤ H) : (H + 20) ^ 2 < 2 * H ^ 2 := by
  nlinarith [sq_nonneg (H - 100)]

private lemma exp_half_gt {H : ℝ} (hH : 20000 ≤ H) : 32000 * H < exp (H / 2) := by
  have hH0 : 0 < H := by linarith
  have hs : (1536000 : ℝ) < H ^ 2 := by nlinarith [sq_nonneg (H - 20000)]
  have hp := mul_pos hH0 (sub_pos.mpr hs)
  have ht := Real.pow_div_factorial_le_exp (H / 2) (show 0 ≤ H / 2 by linarith) 3
  norm_num at ht
  have hh : 32000 * H < (H / 2) ^ 3 / 6 := by nlinarith
  exact hh.trans_le ht

private lemma strict_scalar_gap {H : ℝ} (hH : 20000 ≤ H) :
    1000 * exp (-H) / H < exp (-H / 2) / (16 * (H + 20) ^ 2) := by
  have hH0 : 0 < H := by linarith
  have hw : 0 < 16 * (H + 20) ^ 2 := by positivity
  have he := mul_lt_mul_of_pos_left (exp_half_gt hH) hH0
  have hs := square_cutoff hH
  have hc : 16000 * (H + 20) ^ 2 < H * exp (H / 2) := by nlinarith
  have hce := mul_lt_mul_of_pos_left hc (exp_pos (-H))
  have hexp : exp (-H / 2) = exp (-H) * exp (H / 2) := by
    rw [← exp_add]
    congr 1
    ring
  apply (div_lt_div_iff₀ hH0 hw).2
  rw [hexp]
  nlinarith only [hce]

private lemma exp_neg_sq_le_exp_div {H : ℝ} (hH : 2 ≤ H) :
    exp (-H ^ 2) ≤ exp (-H) / H := by
  have hH0 : 0 < H := by linarith
  have hb : H ≤ exp (H ^ 2 - H) := by
    have he := Real.add_one_le_exp (H ^ 2 - H)
    nlinarith [sq_nonneg (H - 1)]
  have hh := mul_le_mul_of_nonneg_left hb (exp_nonneg (-H ^ 2))
  rw [← exp_add] at hh
  have he : -H ^ 2 + (H ^ 2 - H) = -H := by ring
  rw [he] at hh
  apply (le_div_iff₀ hH0).2
  nlinarith only [hh]

private lemma combined_scalar_budget {H : ℝ} (hH : 20000 ≤ H) :
    (exp (-25 * (H + 20) ^ 2) + exp (-H ^ 2) +
        exp (-4 * (H + 20) ^ 2)) / 6 +
      (7 / 5 : ℝ) * (exp (-H) / H) + 8 * (exp (-H) / H) ≤
        1000 * exp (-H) / H := by
  have he1 : exp (-25 * (H + 20) ^ 2) ≤ exp (-H ^ 2) := by
    apply exp_le_exp.mpr
    nlinarith [sq_nonneg H]
  have he2 : exp (-4 * (H + 20) ^ 2) ≤ exp (-H ^ 2) := by
    apply exp_le_exp.mpr
    nlinarith [sq_nonneg H]
  have he3 := exp_neg_sq_le_exp_div (show 2 ≤ H by linarith)
  have hH0 : 0 < H := by linarith
  have hp : 0 ≤ exp (-H) / H := by positivity
  rw [show 1000 * exp (-H) / H = 1000 * (exp (-H) / H) by ring]
  linarith only [he1, he2, he3, hp]

private lemma epsilon_lower {H A : ℝ} (hA0 : 0 < A) (hAH : A ≤ exp H) :
    exp (-H / 2) / 2 ≤ 1 / (2 * sqrt A) := by
  have hs : sqrt A ≤ exp (H / 2) := by
    have he : sqrt (exp H) = exp (H / 2) := by
      rw [sqrt_eq_rpow, Real.rpow_def_of_pos (exp_pos H), log_exp]
      congr 1
      ring
    rw [← he]
    exact Real.sqrt_le_sqrt hAH
  have hr : 0 < sqrt A := sqrt_pos.mpr hA0
  have hh := one_div_le_one_div_of_le (by positivity : 0 < 2 * sqrt A)
    (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2))
  have he : 1 / (2 * exp (H / 2)) = exp (-H / 2) / 2 := by
    rw [show -H / 2 = -(H / 2) by ring, exp_neg]
    ring
  simpa only [he] using hh

private theorem exists_above_of_mean {μ : Measure ℝ} {J : Set ℝ} {f q : ℝ → ℝ}
    {ε D : ℝ} (hJ : MeasurableSet J)
    (hq : IntegrableOn q J μ) (hf : IntegrableOn (fun y => q y * f y) J μ)
    (hq0 : ∀ y ∈ J, 0 ≤ q y)
    (hmean : |∫ y in J, q y * f y ∂μ| ≤ D)
    (hpay : D < ε * ∫ y in J, q y ∂μ) :
    ∃ y ∈ J, -ε < f y := by
  by_contra hn
  push Not at hn
  have hm : (∫ y in J, q y * f y ∂μ) ≤ -ε * ∫ y in J, q y ∂μ := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on hf (hq.const_mul (-ε)) hJ
    intro y hy
    nlinarith only [mul_le_mul_of_nonneg_left (hn y hy) (hq0 y hy)]
  have hab := neg_abs_le (∫ y in J, q y * f y ∂μ)
  linarith

private theorem paid_scalar_gap {H A : ℝ}
    (hH : 20000 ≤ H) (hA : 10000 ≤ A) (hAH : A ≤ exp H) :
    1000 * exp (-H) / H < (1 / (2 * sqrt A)) *
      ∫ y in Icc H (4 * (H + 20) ^ 2), R y ∂gaussian (H + 20) := by
  have hM := weighted_window_mass hH
  have hε := epsilon_lower (show 0 < A by linarith) hAH
  have hc := mul_le_mul hε hM (by positivity : 0 ≤ 1 / (8 * (H + 20) ^ 2))
    (by positivity : 0 ≤ 1 / (2 * sqrt A))
  have he : (exp (-H / 2) / 2) * (1 / (8 * (H + 20) ^ 2)) =
      exp (-H / 2) / (16 * (H + 20) ^ 2) := by
    field_simp [show H + 20 ≠ 0 by linarith]
    <;> ring
  rw [he] at hc
  exact (strict_scalar_gap hH).trans_le hc

private lemma log_two_pi_bounds : 0 < log (2 * Real.pi) ∧ log (2 * Real.pi) < 3 := by
  constructor
  · exact log_pos (by nlinarith [Real.pi_gt_three])
  · apply (Real.log_lt_iff_lt_exp (by positivity)).mpr
    have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 3
    norm_num [Finset.sum_range_succ] at ht
    nlinarith [Real.pi_lt_four]

private lemma R_upper {y : ℝ} (hy : 1 ≤ y) : R y ≤ 2 / y := by
  have hy0 : 0 < y := by linarith
  dsimp [R]
  apply (div_le_div_iff₀ (sq_pos_of_pos hy0) hy0).mpr
  have hh := mul_le_mul_of_nonneg_left hy hy0.le
  nlinarith only [hh]

private lemma exp_div_antitone {H y : ℝ} (hH : 0 < H) (hy : H ≤ y) :
    exp (-y) / y ≤ exp (-H) / H := by
  exact div_le_div₀ (exp_nonneg _) (exp_le_exp.mpr (neg_le_neg hy)) hH hy

private lemma spectralTail_window_integrable (S : CountableSpectrum) {H : ℝ} (hH : 0 < H) :
    Integrable (spectralTail S) (windowMeasure H) := by
  have hc := (spectral_weighted_integrable S hH).continuousOn_Ici_primitive_Ioi
  exact (hc.mono (fun y hy => hy.1)).integrableOn_compact isCompact_Icc

structure BoundedCorrection where
  value : ℝ → ℝ
  measurable : AEStronglyMeasurable value (volume.restrict (Ioi 0))
  nonneg : ∀ v : ℝ, 0 < v → 0 ≤ value v
  le_one : ∀ v : ℝ, 0 < v → value v ≤ 1

private def correctionIntegrand (C : BoundedCorrection) (v : ℝ) : ℝ :=
  W v * (C.value v - log (2 * Real.pi)) * exp (-v)

private def correctionTail (C : BoundedCorrection) (y : ℝ) : ℝ :=
  ∫ v : ℝ in Ioi y, correctionIntegrand C v

def signedQ (S : CountableSpectrum) (C : BoundedCorrection) (v : ℝ) : ℝ :=
  -(spectralSeries S v).re + (C.value v - log (2 * Real.pi)) * exp (-v)

def signedG (S : CountableSpectrum) (C : BoundedCorrection) (y : ℝ) : ℝ :=
  ∫ v : ℝ in Ioi y, W v * signedQ S C v

private lemma correction_value_bound (C : BoundedCorrection) {v : ℝ} (hv : 0 < v) :
    |C.value v - log (2 * Real.pi)| ≤ 4 := by
  have h0 := C.nonneg v hv
  have h1 := C.le_one v hv
  have hL := log_two_pi_bounds
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma correctionIntegrand_bound (C : BoundedCorrection) {y v : ℝ}
    (hy : 0 < y) (hv : y < v) :
    ‖correctionIntegrand C v‖ ≤ (4 * exp (-y)) * W v := by
  have hv0 : 0 < v := hy.trans hv
  dsimp [correctionIntegrand]
  rw [abs_mul, abs_mul, abs_of_nonneg (W_nonneg hv0.le),
    abs_of_pos (exp_pos _)]
  have hh := mul_le_mul
    (mul_le_mul_of_nonneg_left (correction_value_bound C hv0) (W_nonneg hv0.le))
    (exp_le_exp.mpr (neg_le_neg hv.le)) (exp_nonneg _) (by positivity [W_nonneg hv0.le])
  convert hh using 1 <;> ring

private lemma correction_integrable (C : BoundedCorrection) {y : ℝ} (hy : 0 < y) :
    IntegrableOn (correctionIntegrand C) (Ioi y) := by
  have hT := C.measurable.mono_measure
    (Measure.restrict_mono (Ioi_subset_Ioi hy.le) le_rfl)
  have hW : Measurable W := by unfold W; fun_prop
  refine ((W_tail_integrable hy).const_mul (4 * exp (-y))).mono' ?_ ?_
  · exact (hW.aestronglyMeasurable.mul (hT.sub aestronglyMeasurable_const)).mul
      (show Continuous (fun v : ℝ => exp (-v)) by fun_prop).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact correctionIntegrand_bound C hy hv

private lemma correctionTail_bound (C : BoundedCorrection) {y : ℝ} (hy : 0 < y) :
    |correctionTail C y| ≤ 4 * exp (-y) * R y := by
  have hb := norm_integral_le_of_norm_le
    ((W_tail_integrable hy).const_mul (4 * exp (-y))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact correctionIntegrand_bound C hy hv)
  simpa only [Real.norm_eq_abs, correctionTail, integral_const_mul, W_tail hy] using hb

private lemma correctionTail_window_integrable (C : BoundedCorrection) {H : ℝ} (hH : 0 < H) :
    Integrable (correctionTail C) (windowMeasure H) := by
  have hc := (correction_integrable C hH).continuousOn_Ici_primitive_Ioi
  exact (hc.mono (fun y hy => hy.1)).integrableOn_compact isCompact_Icc

private lemma correctionTail_uniform_bound (C : BoundedCorrection) {H y : ℝ}
    (hH : 1 ≤ H) (hy : H ≤ y) :
    |correctionTail C y| ≤ 8 * (exp (-H) / H) := by
  have hH0 : 0 < H := by linarith
  have hy1 : 1 ≤ y := hH.trans hy
  calc
    _ ≤ 4 * exp (-y) * R y := correctionTail_bound C (hH0.trans_le hy)
    _ ≤ 4 * exp (-y) * (2 / y) :=
      mul_le_mul_of_nonneg_left (R_upper hy1) (by positivity)
    _ = 8 * (exp (-y) / y) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (exp_div_antitone hH0 hy) (by norm_num)

private lemma correction_average_bound (C : BoundedCorrection) {H : ℝ} (hH : 1 ≤ H) :
    |∫ y : ℝ, correctionTail C y ∂windowMeasure H| ≤ 8 * (exp (-H) / H) := by
  have hH0 : 0 < H := by linarith
  have hb := norm_integral_le_of_norm_le_const (μ := windowMeasure H)
    (f := correctionTail C) (C := 8 * (exp (-H) / H)) (by
      change ∀ᵐ y : ℝ ∂(gaussian (H + 20)).restrict (window H), _
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      simpa only [Real.norm_eq_abs] using correctionTail_uniform_bound C hH hy.1)
  exact hb.trans (mul_le_of_le_one_right (by positivity) (windowMeasure_mass H))

private lemma signed_integrand_eq (S : CountableSpectrum) (C : BoundedCorrection) (v : ℝ) :
    W v * signedQ S C v = -((W v : ℂ) * spectralSeries S v).re + correctionIntegrand C v := by
  simp only [signedQ, correctionIntegrand, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

private lemma signed_integrable (S : CountableSpectrum) (C : BoundedCorrection)
    {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun v : ℝ => W v * signedQ S C v) (Ioi y) := by
  have hi := ((spectral_weighted_integrable S hy).re.neg).add (correction_integrable C hy)
  exact hi.congr (ae_of_all _ (fun v => (signed_integrand_eq S C v).symm))

private theorem signedG_decomposition (S : CountableSpectrum) (C : BoundedCorrection)
    {y : ℝ} (hy : 0 < y) :
    signedG S C y = -(spectralTail S y).re + correctionTail C y := by
  dsimp only [signedG, spectralTail, correctionTail]
  simp_rw [signed_integrand_eq]
  have hs := spectral_weighted_integrable S hy
  have ha := integral_add hs.re.neg (correction_integrable C hy)
  simp only [Pi.neg_apply, RCLike.re_eq_complex_re] at ha
  have hr : (∫ v : ℝ in Ioi y, ((W v : ℂ) * spectralSeries S v).re) =
      (∫ v : ℝ in Ioi y, (W v : ℂ) * spectralSeries S v).re := by
    simpa only [RCLike.re_eq_complex_re] using integral_re hs
  rw [ha, integral_neg, hr]

lemma signedG_window_integrable (S : CountableSpectrum) (C : BoundedCorrection)
    {H : ℝ} (hH : 0 < H) : Integrable (signedG S C) (windowMeasure H) := by
  have hc := (signed_integrable S C hH).continuousOn_Ici_primitive_Ioi
  exact (hc.mono (fun y hy => hy.1)).integrableOn_compact isCompact_Icc

private lemma signed_average_components (S : CountableSpectrum) (C : BoundedCorrection)
    {H : ℝ} (hH : 20000 ≤ H) :
    |∫ y : ℝ, signedG S C y ∂windowMeasure H| ≤
      cancellationError H / 6 + (7 / 5 : ℝ) * (exp (-H) / H) + 8 * (exp (-H) / H) := by
  have hH0 : 0 < H := by linarith
  have hS := spectralTail_window_integrable S hH0
  have hC := correctionTail_window_integrable C hH0
  have he : (∫ y : ℝ, signedG S C y ∂windowMeasure H) =
      -(∫ y : ℝ, spectralTail S y ∂windowMeasure H).re +
        ∫ y : ℝ, correctionTail C y ∂windowMeasure H := by
    calc
      _ = ∫ y : ℝ, -(spectralTail S y).re + correctionTail C y ∂windowMeasure H := by
        apply integral_congr_ae
        change ∀ᵐ y : ℝ ∂(gaussian (H + 20)).restrict (window H), _
        filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
        exact signedG_decomposition S C (hH0.trans_le hy.1)
      _ = _ := by
        have ha := integral_add hS.re.neg hC
        simp only [Pi.neg_apply, RCLike.re_eq_complex_re] at ha
        have hr : (∫ y : ℝ, (spectralTail S y).re ∂windowMeasure H) =
            (∫ y : ℝ, spectralTail S y ∂windowMeasure H).re := by
          simpa only [RCLike.re_eq_complex_re] using integral_re hS
        rw [ha, integral_neg, hr]
  rw [he]
  calc
    _ ≤ |-(∫ y : ℝ, spectralTail S y ∂windowMeasure H).re| +
        |∫ y : ℝ, correctionTail C y ∂windowMeasure H| := abs_add_le _ _
    _ ≤ ‖∫ y : ℝ, spectralTail S y ∂windowMeasure H‖ +
        |∫ y : ℝ, correctionTail C y ∂windowMeasure H| := by
      rw [abs_neg]
      exact add_le_add (Complex.abs_re_le_norm _) le_rfl
    _ ≤ _ := add_le_add (spectral_average_bound S hH)
      (correction_average_bound C (by linarith))

theorem full_summed_average_bound (S : CountableSpectrum) (C : BoundedCorrection)
    {H : ℝ} (hH : 20000 ≤ H) :
    |∫ y : ℝ, signedG S C y ∂windowMeasure H| ≤ 1000 * exp (-H) / H := by
  exact (signed_average_components S C hH).trans (combined_scalar_budget hH)

private theorem generic_signed_endpoint (S : CountableSpectrum) (C : BoundedCorrection)
    {H A : ℝ} (hH : 20000 ≤ H) (hA : 10000 ≤ A) (hAH : A ≤ exp H) :
    ∃ y ∈ Icc H (4 * (H + 20) ^ 2),
      -(1 / (2 * sqrt A)) < signedG S C y / R y := by
  have hH0 : 0 < H := by linarith
  have he : (fun y : ℝ => R y * (signedG S C y / R y)) =ᵐ[windowMeasure H] signedG S C := by
    change ∀ᵐ y : ℝ ∂(gaussian (H + 20)).restrict (window H), _
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact mul_div_cancel₀ _ (R_pos (hH0.trans_le hy.1)).ne'
  have hi : IntegrableOn (fun y : ℝ => R y * (signedG S C y / R y))
      (window H) (gaussian (H + 20)) :=
    (signedG_window_integrable S C hH0).congr he.symm
  apply exists_above_of_mean (μ := gaussian (H + 20)) (J := window H)
    (q := R) (f := fun y => signedG S C y / R y)
    (ε := 1 / (2 * sqrt A)) (D := 1000 * exp (-H) / H)
    measurableSet_Icc (R_window_integrable hH) hi
  · intro y hy; exact (R_pos (hH0.trans_le hy.1)).le
  · change |∫ y : ℝ, R y * (signedG S C y / R y) ∂windowMeasure H| ≤ _
    rw [integral_congr_ae he]
    exact full_summed_average_bound S C hH
  · exact paid_scalar_gap hH hA hAH

theorem endpoint_of_complete_representation (S : CountableSpectrum) (C : BoundedCorrection)
    {q : ℝ → ℝ} {H A : ℝ} (hH : 20000 ≤ H) (hA : 10000 ≤ A)
    (hAH : A ≤ exp H) (hq : ∀ v : ℝ, H ≤ v → q v = signedQ S C v) :
    ∃ y ∈ Icc H (4 * (H + 20) ^ 2),
      -(1 / (2 * sqrt A)) < (∫ v : ℝ in Ioi y, W v * q v) / R y := by
  obtain ⟨y, hy, he⟩ := generic_signed_endpoint S C hH hA hAH
  refine ⟨y, hy, ?_⟩
  have hi : (∫ v : ℝ in Ioi y, W v * q v) = signedG S C y := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [hq v (hy.1.trans hv.le)]
  rw [hi]
  exact he

end D5.S3.Weil.Mertens.IntegratedExplicit.SignedGaussianEndpoint
