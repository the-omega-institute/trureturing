/- GID: D5/S3/Analytic/Fourier/ThetaHalfLine
   generality: I
   mirror-B: D5/B/S3/Analytic/Fourier/ThetaHalfLine
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Justify exponential-weighted theta integration by parts on the positive half-line. -/

import D5.S3.Analytic.Fourier.ThetaDifferentialKernel
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
namespace D5.S3.Analytic.Fourier.ThetaHalfLine
open MeasureTheory Set Filter Topology
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering
open D5.S3.Zeros.Jensen.SourceThetaMomentBounds

/-- A Gaussian remains integrable under every real exponential tilt. -/
theorem integrable_tilted_gaussian (b : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-x ^ 2 + b * x)) := by
  have h := (integrable_cexp_quadratic (b := (1 : ℂ)) (by norm_num) (b : ℂ) 0).norm
  convert! h using 1
  ext x
  simp [Complex.norm_exp, Complex.mul_re, pow_two]

private theorem tilted_gaussian_tendsto (b : ℝ) :
    Tendsto (fun x : ℝ => Real.exp (-x ^ 2 + b * x)) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => (x - b) * x) atTop atTop :=
    (tendsto_atTop_add_const_right atTop (-b) tendsto_id).atTop_mul_atTop₀ tendsto_id
  convert! Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h) using 1
  ext x
  dsimp only [Function.comp_apply]
  congr 1
  ring

private theorem weighted_bound {f : ℝ → ℝ} {x : ℝ}
    (hf : |f x| ≤ sourceThetaKernel x) (w : ℂ) :
    ‖(f x : ℂ) * Complex.exp (w * (x : ℂ))‖ ≤
      (∑' n, thetaMajorant n) * Real.exp (-x ^ 2 + w.re * x) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have h := mul_le_mul_of_nonneg_right (hf.trans (source_theta_gaussian_bound x).2)
    (Real.exp_pos ((w * (x : ℂ)).re)).le
  convert! h using 1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [mul_assoc, ← Real.exp_add]

/-- Kernel domination supplies convergence of every complex exponential tilt on the ray. -/
theorem ray_integrable {f : ℝ → ℝ} (hc : Continuous f)
    (hf : ∀ x : ℝ, 0 ≤ x → |f x| ≤ sourceThetaKernel x) (w : ℂ) :
    IntegrableOn (fun x : ℝ => (f x : ℂ) * Complex.exp (w * (x : ℂ))) (Ioi 0) := by
  have hm := ((integrable_tilted_gaussian w.re).const_mul (∑' n, thetaMajorant n)).integrableOn (s := Ioi 0)
  apply hm.mono' ((Complex.continuous_ofReal.comp hc).mul (by fun_prop)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact weighted_bound (hf x (le_of_lt hx)) w

/-- Kernel domination also supplies the endpoint at infinity, for every complex tilt. -/
theorem ray_tendsto {f : ℝ → ℝ}
    (hf : ∀ x : ℝ, 0 ≤ x → |f x| ≤ sourceThetaKernel x) (w : ℂ) :
    Tendsto (fun x : ℝ => (f x : ℂ) * Complex.exp (w * (x : ℂ))) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun x => (∑' n, thetaMajorant n) *
    Real.exp (-x ^ 2 + w.re * x))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact weighted_bound (hf x hx) w
  · simpa using (tilted_gaussian_tendsto w.re).const_mul (∑' n, thetaMajorant n)

/-- The exponentially weighted theta-tail integral. -/
def thetaLaplace (w : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), (psi x : ℂ) * Complex.exp (w * (x : ℂ))

/-- Absolute convergence of the actual theta-tail transform on the positive half-line. -/
theorem psi_integrable (w : ℂ) :
    IntegrableOn (fun x : ℝ => (psi x : ℂ) * Complex.exp (w * (x : ℂ))) (Ioi 0) :=
  ray_integrable (continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_psi x).continuousAt))
    (fun _ hx => (psi_bounds hx).1) w

/-- Absolute convergence for the first derivative needed in integration by parts. -/
theorem psiFirst_integrable (w : ℂ) :
    IntegrableOn (fun x : ℝ => (psiFirst x : ℂ) * Complex.exp (w * (x : ℂ))) (Ioi 0) :=
  ray_integrable (continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_psiFirst x).continuousAt))
    (fun _ hx => (psi_bounds hx).2) w

private theorem kernel_integrable (w : ℂ) :
    IntegrableOn (fun x : ℝ => (sourceThetaKernel x : ℂ) * Complex.exp (w * (x : ℂ))) (Ioi 0) :=
  ray_integrable source_theta_continuous
    (fun x _ => (abs_of_pos (source_theta_gaussian_bound x).1).le) w

private theorem psiSecond_eq (x : ℝ) : psiSecond x = sourceThetaKernel x + psi x / 4 := by
  have h := romikPhi_eq_differential x
  have hd : deriv psi = psiFirst := funext (fun y => (hasDerivAt_psi y).deriv)
  rw [romikPhi_eq_source, hd, (hasDerivAt_psiFirst x).deriv] at h
  linarith

private theorem psiSecond_integrable (w : ℂ) :
    IntegrableOn (fun x : ℝ => (psiSecond x : ℂ) * Complex.exp (w * (x : ℂ))) (Ioi 0) := by
  convert! (kernel_integrable w).add ((psi_integrable w).div_const 4) using 1
  ext x
  rw [psiSecond_eq]
  push_cast
  simp only [Pi.add_apply]
  ring

private theorem cexp_deriv (w : ℂ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (w * (x : ℂ)))
      (w * Complex.exp (w * (x : ℂ))) x := by
  convert! (((hasDerivAt_id (x : ℂ)).const_mul w).cexp).comp_ofReal using 1 <;> simp <;> ring

private theorem ray_ibp {f f' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x)
    (hb : ∀ x, 0 ≤ x → |f x| ≤ sourceThetaKernel x)
    (hi : ∀ w : ℂ, IntegrableOn (fun x : ℝ => (f' x : ℂ) *
      Complex.exp (w * (x : ℂ))) (Ioi 0)) (w : ℂ) :
    (∫ x in Ioi (0 : ℝ), (f' x : ℂ) * Complex.exp (w * (x : ℂ))) =
      -(f 0 : ℂ) - w * ∫ x in Ioi (0 : ℝ), (f x : ℂ) * Complex.exp (w * (x : ℂ)) := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hfi := ray_integrable hc hb w
  have hprod : IntegrableOn (fun x : ℝ => (f x : ℂ) *
      (w * Complex.exp (w * (x : ℂ)))) (Ioi 0) := by
    have he : (fun x : ℝ => (f x : ℂ) * (w * Complex.exp (w * (x : ℂ)))) =
        (fun x : ℝ => w * ((f x : ℂ) * Complex.exp (w * (x : ℂ)))) := by
      ext x
      ring
    rw [he]
    exact Integrable.const_mul hfi w
  have hzero : Tendsto (fun x : ℝ => (f x : ℂ) * Complex.exp (w * (x : ℂ)))
      (𝓝[>] 0) (𝓝 (f 0 : ℂ)) := by
    have hh : Continuous (fun x : ℝ => (f x : ℂ) * Complex.exp (w * (x : ℂ))) :=
      (Complex.continuous_ofReal.comp hc).mul (by fun_prop)
    simpa using (hh.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have h := integral_Ioi_mul_deriv_eq_deriv_mul
    (fun x _ => (hd x).ofReal_comp) (fun x _ => cexp_deriv w x)
    hprod (hi w) hzero (ray_tendsto hb w)
  have he : (∫ x in Ioi (0 : ℝ), (f x : ℂ) * (w * Complex.exp (w * (x : ℂ)))) =
      w * ∫ x in Ioi (0 : ℝ), (f x : ℂ) * Complex.exp (w * (x : ℂ)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    ring
  rw [he, zero_sub] at h
  linear_combination h

/-- Two justified integrations by parts, with the modular boundary derivative. -/
theorem kernel_halfline_integral (w : ℂ) :
    (∫ x in Ioi (0 : ℝ), (sourceThetaKernel x : ℂ) * Complex.exp (w * (x : ℂ))) =
      1 / 4 + w * (psi 0 : ℂ) + (w ^ 2 - 1 / 4) * thetaLaplace w := by
  have h1 := ray_ibp hasDerivAt_psi (fun _ hx => (psi_bounds hx).1) psiFirst_integrable w
  have h2 := ray_ibp hasDerivAt_psiFirst (fun _ hx => (psi_bounds hx).2) psiSecond_integrable w
  have h0 : psiFirst 0 = -1 / 4 := by
    rw [← (hasDerivAt_psi 0).deriv]
    exact psi_deriv_zero
  have hs : (∫ x in Ioi (0 : ℝ), (psiSecond x : ℂ) * Complex.exp (w * (x : ℂ))) =
      (∫ x in Ioi (0 : ℝ), (sourceThetaKernel x : ℂ) * Complex.exp (w * (x : ℂ))) +
      thetaLaplace w / 4 := by
    unfold thetaLaplace
    rw [← integral_div, ← integral_add (kernel_integrable w) ((psi_integrable w).div_const 4)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp only
    rw [psiSecond_eq]
    push_cast
    ring
  rw [h1, h0, hs] at h2
  push_cast at h2
  dsimp only [thetaLaplace] at *
  linear_combination h2

end D5.S3.Analytic.Fourier.ThetaHalfLine
