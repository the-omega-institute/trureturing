/- GID: D5/S3/Fourier/Concentration/GaussianCharacteristicWindow
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/GaussianCharacteristicWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A Gaussian-weighted characteristic function controls mass in a translated real window. -/

import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! Passing from a Fourier bound to the measure of a short interval. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Complex

namespace D5.S3.Fourier.Concentration.GaussianCharacteristicWindow

private theorem gaussian_character_identity (z : ℝ) :
    (∫ t : ℝ, Complex.exp (I * (2 * (z : ℂ)) * t) * Complex.exp (-(t : ℂ) ^ 2)) =
      (Real.sqrt Real.pi : ℂ) * (Real.exp (-z ^ 2) : ℂ) := by
  have hroot : (Real.sqrt Real.pi : ℂ) = (Real.pi : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_nonneg]
    norm_num
  have hquad : -((2 * (z : ℂ)) ^ 2) / (4 * 1) = ((-z ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have h := fourierIntegral_gaussian (b := 1) (by norm_num : 0 < (1 : ℂ).re) (2 * (z : ℂ))
  rw [hquad, div_one, ← hroot, ← Complex.ofReal_exp] at h
  simpa only [neg_mul, one_mul] using h

private theorem gaussian_smoothed_charFun (μ : Measure ℝ) [IsFiniteMeasure μ]
    (b r : ℝ) :
    (Real.sqrt Real.pi : ℂ) * (∫ x, (Real.exp (-((x - b) / r) ^ 2) : ℂ) ∂μ) =
      ∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2) *
        (Complex.exp (-I * (2 * t / r : ℝ) * b) * charFun μ (2 * t / r)) := by
  let F (x t : ℝ) := Complex.exp (I * (2 * ((x - b) / r : ℝ)) * t) *
    Complex.exp (-(t : ℂ) ^ 2)
  have hnorm (x t : ℝ) : ‖F x t‖ = Real.exp (-t ^ 2) := by
    have hphase : I * (2 * ((x - b) / r : ℝ)) * t =
        ((2 * ((x - b) / r) * t : ℝ) : ℂ) * I := by push_cast; ring
    dsimp [F]
    rw [hphase, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_exp]
    norm_cast
  have hF : Integrable (Function.uncurry F) (μ.prod volume) := by
    apply (integrable_norm_iff (by fun_prop)).mp
    have hEq : (fun p : ℝ × ℝ => ‖Function.uncurry F p‖) =
        fun p : ℝ × ℝ => Real.exp (-p.2 ^ 2) := by
      funext p
      exact hnorm p.1 p.2
    rw [hEq]
    exact ((show Integrable (fun t : ℝ => Real.exp (-t ^ 2)) by
      simpa using integrable_exp_neg_mul_sq (by norm_num : 0 < (1 : ℝ)))).comp_snd μ
  rw [← integral_const_mul]
  calc
    _ = ∫ x, (∫ t, F x t) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simpa only [F, ofReal_mul, ofReal_ofNat] using
        (gaussian_character_identity ((x - b) / r)).symm
    _ = ∫ t : ℝ, (∫ x, F x t ∂μ) := integral_integral_swap hF
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [charFun_apply_real, ← integral_const_mul (r := Complex.exp (-I * (2 * t / r : ℝ) * b)),
        ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [F]
      rw [mul_comm (Complex.exp (I * (2 * ((x - b) / r : ℝ)) * t)),
        ← Complex.exp_add (-I * (2 * t / r : ℝ) * b)]
      congr 2
      push_cast
      ring

/-- The mass of a closed translated interval is controlled by a Gaussian-weighted
average of the modulus of the characteristic function. -/
theorem measureReal_closedWindow_le_gaussian_charFun
    (μ : Measure ℝ) [IsFiniteMeasure μ] (b : ℝ) {r : ℝ} (hr : 0 < r) :
    Real.sqrt Real.pi * μ.real {x | |x - b| ≤ r} ≤
      Real.exp 1 * ∫ t : ℝ, Real.exp (-t ^ 2) * ‖charFun μ (2 * t / r)‖ := by
  let K (x : ℝ) := Real.exp (-((x - b) / r) ^ 2)
  let W : Set ℝ := {x | |x - b| ≤ r}
  have hK : Integrable K μ :=
    (integrable_const (1 : ℝ)).mono' (by dsimp [K]; fun_prop)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
  have hW : MeasurableSet W := measurableSet_le (by fun_prop) measurable_const
  have hmass : μ.real W ≤ Real.exp 1 * ∫ x, K x ∂μ := by
    rw [← integral_const_mul]
    calc
      _ = ∫ x, W.indicator (fun _ => (1 : ℝ)) x ∂μ := by
        rw [integral_indicator hW]
        simp
      _ ≤ _ := by
        apply integral_mono (integrable_const _ |>.indicator hW) (hK.const_mul _)
        intro x
        by_cases hx : x ∈ W
        · have habs : |(x - b) / r| ≤ 1 := by
            rw [abs_div, abs_of_pos hr, div_le_iff₀ hr, one_mul]
            exact hx
          have hsquare : ((x - b) / r) ^ 2 ≤ 1 := by
            simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) habs 2
          rw [indicator_of_mem hx]
          dsimp [K]
          rw [← Real.exp_add]
          calc
            (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
            _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
        · rw [indicator_of_notMem hx]
          exact mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
  have hsmooth := gaussian_smoothed_charFun μ b r
  change (Real.sqrt Real.pi : ℂ) * (∫ x, (K x : ℂ) ∂μ) = _ at hsmooth
  rw [integral_complex_ofReal (f := K) (μ := μ)] at hsmooth
  have hbound : Real.sqrt Real.pi * (∫ x, K x ∂μ) ≤
      ∫ t : ℝ, Real.exp (-t ^ 2) * ‖charFun μ (2 * t / r)‖ := by
    have hnorm :
        ‖(Real.sqrt Real.pi : ℂ) * Complex.ofReal (∫ x, K x ∂μ)‖ =
          Real.sqrt Real.pi * (∫ x, K x ∂μ) := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.norm_of_nonneg (integral_nonneg fun x => Real.exp_nonneg _)]
    rw [← hnorm, hsmooth]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    apply integral_congr_ae
    filter_upwards [] with t
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
    have hzero : (-I * (2 * t / r : ℝ) * b : ℂ).re = 0 := by
      simp
    rw [hzero, Real.exp_zero, one_mul]
    norm_cast
  calc
    _ ≤ Real.sqrt Real.pi * (Real.exp 1 * ∫ x, K x ∂μ) :=
      mul_le_mul_of_nonneg_left hmass (Real.sqrt_nonneg _)
    _ = Real.exp 1 * (Real.sqrt Real.pi * ∫ x, K x ∂μ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg _)

end D5.S3.Fourier.Concentration.GaussianCharacteristicWindow
