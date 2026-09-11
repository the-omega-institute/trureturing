/- GID: D5/S3/Analytic/Fourier/XiThetaTransform
   generality: I
   mirror-B: D5/B/S3/Analytic/Fourier/XiThetaTransform
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relate the original theta Fourier integral to the pole-free completed zeta. -/

import D5.S3.Analytic.Fourier.ThetaDifferentialKernel
import D5.S3.Analytic.CompletedZetaMellinReconstruction
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
namespace D5.S3.Analytic.Fourier.XiThetaTransform
open MeasureTheory Set Filter Topology
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel
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

/-- A Gaussian remains integrable after an arbitrary real exponential tilt. -/
private theorem integrable_tilted_gaussian (b : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-x ^ 2 + b * x)) := by
  have h := (integrable_cexp_quadratic (b := (1 : ℂ)) (by norm_num) (b : ℂ) 0).norm
  convert! h using 1
  ext x
  simp [Complex.norm_exp, Complex.mul_re, pow_two]

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

end D5.S3.Analytic.Fourier.XiThetaTransform
