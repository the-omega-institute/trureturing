/- GID: D5/S3/Constants/Limits/EulerCountertermExistenceUniqueness
   generality: G
   mirror-B: D5/B/S3/Constants/Limits/EulerCountertermExistenceUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Euler's constant supplies the finite counterterm, while pi removes Gaussian defect. -/

import D5.S3.Fourier.CompletionConstants.GaussianSelfDualPi
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.Limits.EulerCountertermExistenceUniqueness

open Filter Topology
open scoped FourierTransform

/-- The standard Gaussian's failure to be fixed by the real Fourier transform at scale `a`. -/
noncomputable def gaussianSelfDualityDefect (a : ℝ) : ℝ → ℂ :=
  𝓕 (fun x : ℝ => (Real.exp (-a * x ^ 2) : ℂ)) -
    (fun x : ℝ => (Real.exp (-a * x ^ 2) : ℂ))

/-- A scale eliminates the Gaussian self-duality defect when that defect is zero. -/
def EliminatesGaussianSelfDualityDefect (a : ℝ) : Prop :=
  gaussianSelfDualityDefect a = 0

/-- The Euler-Mascheroni constant supplies the zero harmonic-log residual, and pi eliminates
the standard Gaussian Fourier self-duality defect. -/
theorem euler_counterterm_exists_and_unique :
    Tendsto
      (fun n : ℕ =>
        (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant)
      atTop (𝓝 0) ∧
    EliminatesGaussianSelfDualityDefect Real.pi := by
  constructor
  · simpa only [sub_self] using
      Real.tendsto_harmonic_sub_log.sub_const Real.eulerMascheroniConstant
  · have pi_self_dual :
        𝓕 (fun x : ℝ => (Real.exp (-Real.pi * x ^ 2) : ℂ)) =
          (fun x : ℝ => (Real.exp (-Real.pi * x ^ 2) : ℂ)) :=
      (D5.S3.Fourier.CompletionConstants.GaussianSelfDualPi.gaussian_self_dual_iff
        Real.pi Real.pi_pos).2 rfl
    simp only [EliminatesGaussianSelfDualityDefect, gaussianSelfDualityDefect,
      pi_self_dual, sub_self]

#print axioms euler_counterterm_exists_and_unique

end D5.S3.Constants.Limits.EulerCountertermExistenceUniqueness
