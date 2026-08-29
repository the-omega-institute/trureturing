/- GID: D5/S3/Analytic/ZetaCriticalCurvature/CriticalNormalEvenness
   generality: G
   mirror-B: D5/B/S3/Analytic/ZetaCriticalCurvature/CriticalNormalEvenness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reflection-even scalar potentials have zero first normal derivative
     at the fixed axis. -/

import Mathlib

/-!
This module proves the symmetry obstruction abstractly. It does not identify
the potential with `log |xi|`; that specialization requires a separately proved
functional equation and a zero-free neighborhood where the logarithm is
ordinary differentiable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ZetaCriticalCurvature.CriticalNormalEvenness

/-- A differentiable even real function has zero derivative at the reflection
fixed point. -/
theorem even_hasDerivAt_zero
    {V : ℝ → ℝ} {d : ℝ}
    (hDerivative : HasDerivAt V d 0)
    (hEven : ∀ u : ℝ, V (-u) = V u) :
    d = 0 := by
  have hNeg : HasDerivAt (fun u : ℝ => -u) (-1) 0 := by
    simpa using (hasDerivAt_neg (𝕜 := ℝ) 0)
  have hReflected : HasDerivAt (fun u : ℝ => V (-u)) (-d) 0 := by
    have hDerivative' : HasDerivAt V d (-0) := by
      simpa using hDerivative
    have hComp := hDerivative'.comp 0 hNeg
    simpa [Function.comp_def] using hComp
  have hSame : (fun u : ℝ => V (-u)) = V := by
    funext u
    exact hEven u
  rw [hSame] at hReflected
  have hUnique := hReflected.unique hDerivative
  linarith

/-- `deriv` formulation of the same reflection obstruction. -/
theorem deriv_even_zero
    {V : ℝ → ℝ}
    (hDifferentiable : DifferentiableAt ℝ V 0)
    (hEven : ∀ u : ℝ, V (-u) = V u) :
    deriv V 0 = 0 := by
  exact even_hasDerivAt_zero hDifferentiable.hasDerivAt hEven

/-- Parameterized potential version. For every fixed tangential coordinate
`t`, normal reflection symmetry removes the first normal derivative. -/
theorem critical_normal_derivative_zero
    {V : ℝ → ℝ → ℝ} {t d : ℝ}
    (hDerivative : HasDerivAt (fun u : ℝ => V u t) d 0)
    (hReflection : ∀ u : ℝ, V (-u) t = V u t) :
    d = 0 := by
  exact even_hasDerivAt_zero hDerivative hReflection

/-- Pointwise family formulation. -/
theorem critical_normal_deriv_zero
    {V : ℝ → ℝ → ℝ}
    (hDifferentiable : ∀ t : ℝ,
      DifferentiableAt ℝ (fun u : ℝ => V u t) 0)
    (hReflection : ∀ u t : ℝ, V (-u) t = V u t) :
    ∀ t : ℝ, deriv (fun u : ℝ => V u t) 0 = 0 := by
  intro t
  exact deriv_even_zero (hDifferentiable t) (fun u => hReflection u t)

/-- Cancellation is exact and does not depend on a smallness estimate. -/
example {V : ℝ → ℝ} {d : ℝ}
    (hDerivative : HasDerivAt V d 0)
    (hEven : ∀ u : ℝ, V (-u) = V u) :
    |d| = 0 := by
  rw [even_hasDerivAt_zero hDerivative hEven, abs_zero]

#print axioms even_hasDerivAt_zero
#print axioms deriv_even_zero
#print axioms critical_normal_derivative_zero
#print axioms critical_normal_deriv_zero

end D5.S3.Analytic.ZetaCriticalCurvature.CriticalNormalEvenness
