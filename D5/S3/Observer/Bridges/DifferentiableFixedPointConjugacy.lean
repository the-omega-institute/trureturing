/- GID: D5/S3/Observer/Bridges/DifferentiableFixedPointConjugacy
   generality: G
   mirror-B: D5/B/S3/Observer/Bridges/DifferentiableFixedPointConjugacy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A differentiable semiconjugacy intertwines fixed-point multipliers, and a nondegenerate bridge preserves the one-dimensional stability type. -/

import D5.S3.Observer.Bridges.FixedPointSemiconjugacy
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
At a common fixed point, the chain rule gives

`dBridge * dSource = dTarget * dBridge`.

In one real dimension a nonzero bridge derivative can be cancelled.  This is
the local mathematical content of a differentiable “wormhole”: multiplier and
attracting, neutral, or repelling type are transported by a nondegenerate
coordinate bridge.  A singular or many-to-one observer may erase directions,
so no reflection theorem is stated without the nonzero derivative hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Bridges.DifferentiableFixedPointConjugacy

/-- The chain rule intertwines the two local multipliers at a fixed point. -/
theorem derivative_intertwining_at_fixed_point
    {bridge sourceStep targetStep : ℝ → ℝ} {x dBridge dSource dTarget : ℝ}
    (hSemiconj : Function.Semiconj bridge sourceStep targetStep)
    (hFixed : Function.IsFixedPt sourceStep x)
    (hBridge : HasDerivAt bridge dBridge x)
    (hSource : HasDerivAt sourceStep dSource x)
    (hTarget : HasDerivAt targetStep dTarget (bridge x)) :
    dBridge * dSource = dTarget * dBridge := by
  have hBridgeAtSource : HasDerivAt bridge dBridge (sourceStep x) := by
    simpa [Function.IsFixedPt, hFixed] using hBridge
  have hLeft :
      HasDerivAt (fun y : ℝ => bridge (sourceStep y))
        (dBridge * dSource) x :=
    hBridgeAtSource.comp x hSource
  have hRight :
      HasDerivAt (fun y : ℝ => targetStep (bridge y))
        (dTarget * dBridge) x :=
    hTarget.comp x hBridge
  have hFunctions :
      (fun y : ℝ => bridge (sourceStep y)) =
        (fun y : ℝ => targetStep (bridge y)) := by
    funext y
    exact hSemiconj y
  rw [hFunctions] at hLeft
  exact hLeft.unique hRight

/-- A nonzero bridge derivative forces equality of the one-dimensional local
multipliers. -/
theorem multiplier_eq_of_nondegenerate_bridge
    {bridge sourceStep targetStep : ℝ → ℝ} {x dBridge dSource dTarget : ℝ}
    (hSemiconj : Function.Semiconj bridge sourceStep targetStep)
    (hFixed : Function.IsFixedPt sourceStep x)
    (hBridge : HasDerivAt bridge dBridge x)
    (hSource : HasDerivAt sourceStep dSource x)
    (hTarget : HasDerivAt targetStep dTarget (bridge x))
    (hNondegenerate : dBridge ≠ 0) :
    dSource = dTarget := by
  have hIntertwining := derivative_intertwining_at_fixed_point
    hSemiconj hFixed hBridge hSource hTarget
  apply mul_left_cancel₀ hNondegenerate
  simpa [mul_comm] using hIntertwining

/-- Strict attraction is preserved by a nondegenerate differentiable bridge. -/
theorem attracting_multiplier_iff
    {bridge sourceStep targetStep : ℝ → ℝ} {x dBridge dSource dTarget : ℝ}
    (hSemiconj : Function.Semiconj bridge sourceStep targetStep)
    (hFixed : Function.IsFixedPt sourceStep x)
    (hBridge : HasDerivAt bridge dBridge x)
    (hSource : HasDerivAt sourceStep dSource x)
    (hTarget : HasDerivAt targetStep dTarget (bridge x))
    (hNondegenerate : dBridge ≠ 0) :
    |dSource| < 1 ↔ |dTarget| < 1 := by
  rw [multiplier_eq_of_nondegenerate_bridge hSemiconj hFixed hBridge
    hSource hTarget hNondegenerate]

/-- Neutrality is likewise a coordinate-invariant statement under the same
nondegeneracy hypothesis. -/
theorem neutral_multiplier_iff
    {bridge sourceStep targetStep : ℝ → ℝ} {x dBridge dSource dTarget : ℝ}
    (hSemiconj : Function.Semiconj bridge sourceStep targetStep)
    (hFixed : Function.IsFixedPt sourceStep x)
    (hBridge : HasDerivAt bridge dBridge x)
    (hSource : HasDerivAt sourceStep dSource x)
    (hTarget : HasDerivAt targetStep dTarget (bridge x))
    (hNondegenerate : dBridge ≠ 0) :
    |dSource| = 1 ↔ |dTarget| = 1 := by
  rw [multiplier_eq_of_nondegenerate_bridge hSemiconj hFixed hBridge
    hSource hTarget hNondegenerate]

/-- Repulsion is also preserved. -/
theorem repelling_multiplier_iff
    {bridge sourceStep targetStep : ℝ → ℝ} {x dBridge dSource dTarget : ℝ}
    (hSemiconj : Function.Semiconj bridge sourceStep targetStep)
    (hFixed : Function.IsFixedPt sourceStep x)
    (hBridge : HasDerivAt bridge dBridge x)
    (hSource : HasDerivAt sourceStep dSource x)
    (hTarget : HasDerivAt targetStep dTarget (bridge x))
    (hNondegenerate : dBridge ≠ 0) :
    1 < |dSource| ↔ 1 < |dTarget| := by
  rw [multiplier_eq_of_nondegenerate_bridge hSemiconj hFixed hBridge
    hSource hTarget hNondegenerate]

#print axioms derivative_intertwining_at_fixed_point
#print axioms multiplier_eq_of_nondegenerate_bridge
#print axioms attracting_multiplier_iff
#print axioms neutral_multiplier_iff
#print axioms repelling_multiplier_iff

end D5.S3.Observer.Bridges.DifferentiableFixedPointConjugacy
