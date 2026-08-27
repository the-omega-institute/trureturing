/- GID: D5/S3/Fourier/CompletionConstants/GaussianSelfDualPi
   generality: G
   mirror-B: D5/B/S3/Fourier/CompletionConstants/GaussianSelfDualPi
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A positive real Gaussian is strictly Fourier self-dual exactly at scale pi. -/

/- Library-search audit trail (2026-08-27):
   * D5 searches found `GaussianThetaTransformation`, which uses the same pinned
     Mathlib Gaussian Fourier theory, but no theorem characterizing the unique
     self-dual scale.
   * Pinned Mathlib supplies `fourier_gaussian_pi` for sufficiency and
     `integral_gaussian` for the value-at-zero necessity argument; both are
     applied below instead of re-proving either analytic identity.
   * Loogle returned `fourier_gaussian_pi` exactly. LeanSearch and Reservoir
     API probes returned HTTP 404, while unauthenticated GitHub code search
     returned HTTP 401.
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

namespace D5.S3.Fourier.CompletionConstants.GaussianSelfDualPi

open MeasureTheory
open scoped FourierTransform

/-- Under the standard real Fourier convention with kernel `exp (-2 * pi * i * x * xi)`,
the positive Gaussian `x |-> exp (-a * x^2)` is strictly self-dual exactly when `a = pi`. -/
theorem gaussian_self_dual_iff (a : ℝ) (ha : 0 < a) :
    𝓕 (fun x : ℝ ↦ (Real.exp (-a * x ^ 2) : ℂ)) =
        (fun x : ℝ ↦ (Real.exp (-a * x ^ 2) : ℂ)) ↔
      a = Real.pi := by
  let g : ℝ → ℂ := fun x ↦ (Real.exp (-a * x ^ 2) : ℂ)
  change 𝓕 g = g ↔ a = Real.pi
  constructor
  · intro hself
    have hmass : (𝓕 g) 0 = (Real.sqrt (Real.pi / a) : ℂ) := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
        one_smul]
      change (∫ x : ℝ, (Real.exp (-a * x ^ 2) : ℂ)) =
        (Real.sqrt (Real.pi / a) : ℂ)
      rw [integral_complex_ofReal, integral_gaussian]
    have hsqrt_complex : (Real.sqrt (Real.pi / a) : ℂ) = 1 := by
      rw [← hmass, hself]
      simp [g]
    have hsqrt_real : Real.sqrt (Real.pi / a) = 1 := by
      exact_mod_cast hsqrt_complex
    have hratio : Real.pi / a = 1 := Real.sqrt_eq_one.mp hsqrt_real
    exact ((div_eq_one_iff_eq ha.ne').mp hratio).symm
  · rintro rfl
    simpa [g] using (fourier_gaussian_pi (b := (1 : ℂ)) (by norm_num))

/-- Reverse probe: the public proposition recovers the nontrivial scale identity. -/
example (a : ℝ) (ha : 0 < a)
    (hself :
      𝓕 (fun x : ℝ ↦ (Real.exp (-a * x ^ 2) : ℂ)) =
        (fun x : ℝ ↦ (Real.exp (-a * x ^ 2) : ℂ))) :
    a = Real.pi :=
  (gaussian_self_dual_iff a ha).mp hself

/-- Trivialization probe: the zero scale cannot satisfy the theorem's sourced positive domain. -/
example :
    ¬ (0 < (0 : ℝ) ∧
      𝓕 (fun x : ℝ ↦ (Real.exp (-(0 : ℝ) * x ^ 2) : ℂ)) =
        (fun x : ℝ ↦ (Real.exp (-(0 : ℝ) * x ^ 2) : ℂ))) := by
  simp

#print axioms gaussian_self_dual_iff

end D5.S3.Fourier.CompletionConstants.GaussianSelfDualPi
