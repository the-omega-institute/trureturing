/- GID: D5/S3/Analytic/Adelic/ZeroCompletionVelocity
   generality: G
   mirror-B: D5/B/S3/Analytic/Adelic/ZeroCompletionVelocity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A simple zero thread moves by the ratio of completion and spatial derivatives. -/

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.Basic

/- Library-search audit trail (2026-08-30):
   * Frozen D5 searches for zero velocity, implicit derivatives, derivative
     quotients, and joint `fst`/`snd` derivative shapes found no exact owner.
   * The nearby analytic-adelic jet modules concern finite resolvent pencils
     and toroidal jet depth, not motion of a zero under a completion parameter.
   * Pinned Mathlib provides the general implicit-function construction and
     its operator-valued derivative formula. For the source's already-given
     zero thread, the thinner exact ingredients are `HasFDerivAt.comp_hasDerivAt`,
     `HasDerivAt.prodMk`, and uniqueness of derivatives; they are applied here.
   * No new definition or abbreviation is introduced, so no source primitive
     is forked. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Adelic.ZeroCompletionVelocity

/-- Along a differentiable zero thread, a nonzero spatial derivative makes
the zero velocity equal to minus the completion derivative divided by the
spatial derivative. The displayed Frechet derivative exposes the two partial
derivatives as its coefficients on the completion and spatial coordinates. -/
theorem zero_completion_velocity
    (F : ℝ -> ℂ -> ℂ) (rho : ℝ -> ℂ) (tau : ℝ)
    (completionDerivative spatialDerivative velocity : ℂ)
    (hF : HasFDerivAt (fun p : ℝ × ℂ => F p.1 p.2)
      ((ContinuousLinearMap.fst ℝ ℝ ℂ).smulRight completionDerivative +
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) spatialDerivative).restrictScalars ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ ℂ))
      (tau, rho tau))
    (hRho : HasDerivAt rho velocity tau)
    (hZero : ∀ u, F u (rho u) = 0)
    (hSimple : spatialDerivative ≠ 0) :
    velocity = -completionDerivative / spatialDerivative := by
  have hPath : HasDerivAt (fun u => (u, rho u)) (1, velocity) tau :=
    (hasDerivAt_id tau).prodMk hRho
  have hCombined :
      HasDerivAt (fun u => F u (rho u))
        (completionDerivative + spatialDerivative * velocity) tau := by
    simpa [Function.comp_def, mul_comm] using hF.comp_hasDerivAt tau hPath
  have hDerivativeZero : completionDerivative + spatialDerivative * velocity = 0 := by
    rw [show (fun u => F u (rho u)) = fun _ => 0 by
      funext u
      exact hZero u] at hCombined
    exact hCombined.unique (hasDerivAt_const tau 0)
  exact (eq_div_iff hSimple).2 (by linear_combination hDerivativeZero)

#print axioms zero_completion_velocity

end D5.S3.Analytic.Adelic.ZeroCompletionVelocity
