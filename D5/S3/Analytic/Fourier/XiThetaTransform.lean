/- GID: D5/S3/Analytic/Fourier/XiThetaTransform
   generality: I
   mirror-B: D5/B/S3/Analytic/Fourier/XiThetaTransform
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relate the original theta Fourier integral to the pole-free completed zeta. -/

import D5.S3.Analytic.Fourier.ThetaHalfLine
import D5.S3.Analytic.CompletedZetaMellinReconstruction
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
namespace D5.S3.Analytic.Fourier.XiThetaTransform
open MeasureTheory Set Filter Topology
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open D5.S3.Analytic.Fourier.ThetaHalfLine
open D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering
open D5.S3.Zeros.Jensen.SourceThetaMomentBounds
open D5.S3.Zeros.CompletedZeta

/-- The symmetric Mellin integral of the original theta tail. -/
def thetaMellin (s : ℂ) : ℂ := ∫ t in Ioi (1 : ℝ),
  (((theta t : ℂ) - 1) / 2) *
    ((t : ℂ) ^ (s / 2) + (t : ℂ) ^ ((1 - s) / 2)) / (t : ℂ)

/-- Cancel the explicit pole terms additively, including at zero and one. -/
theorem thetaMellin_eq_completed (s : ℂ) : thetaMellin s = completedRiemannZeta₀ s := by
  have h := D5.S3.Analytic.CompletedZetaMellinReconstruction.completed_zeta_mellin_reconstruction.2.1 s
  change completedRiemannZeta s = thetaMellin s - 1 / s - 1 / (1 - s) at h
  rw [completedRiemannZeta_eq] at h
  exact (sub_left_inj.mp (sub_left_inj.mp h)).symm

/-- The fixed theta kernel has an absolutely convergent Fourier integral at every complex point. -/
theorem source_theta_fourier_integrable (z : ℂ) :
    Integrable (fun x : ℝ => (sourceThetaKernel x : ℂ) * Complex.exp (Complex.I * z * (x : ℂ))) := by
  have hm := (integrable_tilted_gaussian (-z.im)).const_mul (∑' n, thetaMajorant n)
  apply hm.mono' ((Complex.continuous_ofReal.comp source_theta_continuous).mul
    (by fun_prop)).aestronglyMeasurable
  filter_upwards [] with x
  dsimp only [Pi.mul_apply, Function.comp_apply]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (source_theta_gaussian_bound x).1, Complex.norm_exp]
  have h := mul_le_mul_of_nonneg_right (source_theta_gaussian_bound x).2
    (Real.exp_pos ((Complex.I * z * (x : ℂ)).re)).le
  convert! h using 1
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, one_mul, sub_zero, mul_zero]
  rw [mul_assoc, ← Real.exp_add]
  ring_nf

private theorem cpow_exp_real (a : ℝ) (b : ℂ) :
    (Real.exp a : ℂ) ^ b = Complex.exp ((a : ℂ) * b) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_ne_zero a)),
    ← Complex.ofReal_log (Real.exp_pos a).le, Real.log_exp]

private theorem mellin_substitution_integrand (w : ℂ) (x : ℝ) :
    (Real.exp (2 * x) : ℂ) *
      ((((theta (Real.exp (2 * x)) : ℂ) - 1) / 2) *
        ((Real.exp (2 * x) : ℂ) ^ (((1 / 2 : ℂ) + w) / 2) +
          (Real.exp (2 * x) : ℂ) ^ ((1 - ((1 / 2 : ℂ) + w)) / 2)) /
        (Real.exp (2 * x) : ℂ)) =
      (psi x : ℂ) * Complex.exp (w * (x : ℂ)) +
      (psi x : ℂ) * Complex.exp (-w * (x : ℂ)) := by
  have he : (Real.exp (2 * x) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_ne_zero (2 * x))
  rw [cpow_exp_real, cpow_exp_real]
  have hp : Complex.exp ((2 * x : ℝ) * (((1 / 2 : ℂ) + w) / 2)) =
      (Real.exp (x / 2) : ℂ) * Complex.exp (w * (x : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hn : Complex.exp ((2 * x : ℝ) * ((1 - ((1 / 2 : ℂ) + w)) / 2)) =
      (Real.exp (x / 2) : ℂ) * Complex.exp (-w * (x : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hp, hn]
  unfold psi
  push_cast
  field_simp

/-- The logarithmic substitution connects the symmetric Mellin integral to both theta tails. -/
theorem thetaMellin_center (w : ℂ) :
    thetaMellin ((1 / 2 : ℂ) + w) = 2 * (thetaLaplace w + thetaLaplace (-w)) := by
  let g : ℝ → ℂ := fun t => (((theta t : ℂ) - 1) / 2) *
    ((t : ℂ) ^ (((1 / 2 : ℂ) + w) / 2) +
      (t : ℂ) ^ ((1 - ((1 / 2 : ℂ) + w)) / 2)) / (t : ℂ)
  have he := integral_comp_exp_Ioi g 0
  have hs := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp x • g (Real.exp x))
    0 (by norm_num : (0 : ℝ) < 2)
  simp only [Real.exp_zero] at he
  simp only [mul_zero] at hs
  rw [he] at hs
  have hi : (∫ x in Ioi (0 : ℝ), Real.exp (2 * x) • g (Real.exp (2 * x))) =
      thetaLaplace w + thetaLaplace (-w) := by
    unfold thetaLaplace
    rw [← integral_add (psi_integrable w) (psi_integrable (-w))]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    exact mellin_substitution_integrand w x
  rw [hi] at hs
  change thetaLaplace w + thetaLaplace (-w) = (2 : ℝ)⁻¹ • thetaMellin ((1 / 2 : ℂ) + w) at hs
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_ofNat] at hs
  linear_combination -2 * hs

/-- The all-complex Fourier integral is the actual entire xi function. -/
theorem source_theta_fourier_eq_xi (z : ℂ) :
    (∫ x : ℝ, (sourceThetaKernel x : ℂ) * Complex.exp (Complex.I * z * (x : ℂ))) =
      xiReading ((1 / 2 : ℂ) + Complex.I * z) := by
  let f : ℝ → ℂ := fun x => (sourceThetaKernel x : ℂ) * Complex.exp (Complex.I * z * (x : ℂ))
  have hi : Integrable f := source_theta_fourier_integrable z
  have hs := intervalIntegral.integral_Iic_add_Ioi (hi.integrableOn (s := Iic 0)) (hi.integrableOn (s := Ioi 0))
  have hn := integral_comp_neg_Ioi 0 f
  simp only [neg_zero] at hn
  rw [← hn] at hs
  have hp : (∫ x in Ioi (0 : ℝ), f x) = 1 / 4 + (Complex.I * z) * (psi 0 : ℂ) +
      ((Complex.I * z) ^ 2 - 1 / 4) * thetaLaplace (Complex.I * z) := kernel_halfline_integral _
  have hm : (∫ x in Ioi (0 : ℝ), f (-x)) = 1 / 4 + (- (Complex.I * z)) * (psi 0 : ℂ) +
      ((-(Complex.I * z)) ^ 2 - 1 / 4) * thetaLaplace (-(Complex.I * z)) := by
    convert! kernel_halfline_integral (-(Complex.I * z)) using 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp [f]
    rw [source_theta_even]
    push_cast
    congr 2
    ring
  rw [hp, hm] at hs
  have hM := thetaMellin_center (Complex.I * z)
  rw [thetaMellin_eq_completed] at hM
  unfold xiReading
  rw [hM, ← hs]
  ring

/-- The existing constant-coefficient premise follows from the actual Fourier identity at zero. -/
theorem source_theta_coefficient_zero : sourceThetaCoefficient 0 = 1 := by
  have h := source_theta_fourier_eq_xi 0
  simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one, add_zero] at h
  have hm : (∫ x : ℝ, sourceThetaKernel x) = (xiReading (1 / 2 : ℂ)).re := by
    have hr := congrArg Complex.re h
    simpa only [integral_complex_ofReal, Complex.ofReal_re] using hr
  have hp : 0 < ∫ x : ℝ, sourceThetaKernel x := by
    simpa only [Nat.mul_zero, pow_zero, one_mul] using (source_theta_raw_moments 0).2
  simp only [sourceThetaCoefficient, sourceThetaMoment, sourceThetaDensity, Nat.mul_zero,
    pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, div_one, integral_div, hm]
  exact div_self (ne_of_gt (hm ▸ hp))

/-- Unconditional mass, positive xi denominator and positive normalized theta coefficients. -/
theorem source_theta_normalized :
    (xiReading (1 / 2 : ℂ)).re = ∫ x : ℝ, sourceThetaKernel x ∧
    0 < (xiReading (1 / 2 : ℂ)).re ∧
    (∫ x : ℝ, sourceThetaDensity x) = 1 ∧
    (∀ k : ℕ, 0 < sourceThetaCoefficient k) :=
  source_theta_normalization source_theta_coefficient_zero

end D5.S3.Analytic.Fourier.XiThetaTransform
