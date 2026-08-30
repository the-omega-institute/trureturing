/- GID: D5/S3/Analytic/ZetaCompletionFlow/SimpleZeroCompletionVelocity
   generality: G
   mirror-B: D5/B/S3/Analytic/ZetaCompletionFlow/SimpleZeroCompletionVelocity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nondegenerate zero-thread chain equation determines its completion velocity by the ratio of completion and state derivatives. -/

import Mathlib

/-!
This owner closes the algebraic step of the zero-velocity formula. A later
analytic owner must supply the chain equation from differentiability of a
parameterized family. The nonzero state derivative is explicit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ZetaCompletionFlow.SimpleZeroCompletionVelocity

universe u

variable {K : Type u} [Field K]

/-- Velocity predicted by the completion-direction and state-direction
partials at a simple zero. -/
def zeroCompletionVelocity (completionDerivative stateDerivative : K) : K :=
  -completionDerivative / stateDerivative

/-- Algebraic extraction of the simple-zero completion velocity from the chain
rule identity. -/
theorem zero_completion_velocity_eq_of_chain
    {completionDerivative stateDerivative velocity : K}
    (hState : stateDerivative ≠ 0)
    (hChain : completionDerivative + stateDerivative * velocity = 0) :
    velocity = zeroCompletionVelocity completionDerivative stateDerivative := by
  have hMul : stateDerivative * velocity = -completionDerivative := by
    calc
      stateDerivative * velocity =
          (completionDerivative + stateDerivative * velocity) -
            completionDerivative := by ring
      _ = 0 - completionDerivative := by rw [hChain]
      _ = -completionDerivative := by ring
  unfold zeroCompletionVelocity
  apply (eq_div_iff hState).2
  simpa [mul_comm] using hMul

/-- Substitution back into the chain equation. -/
theorem zero_completion_velocity_satisfies_chain
    (completionDerivative stateDerivative : K)
    (hState : stateDerivative ≠ 0) :
    completionDerivative + stateDerivative *
      zeroCompletionVelocity completionDerivative stateDerivative = 0 := by
  unfold zeroCompletionVelocity
  field_simp [hState]
  ring

/-- Common nonzero rescaling of the analytic family leaves zero velocity
unchanged. -/
theorem zero_completion_velocity_scale_invariant
    (c completionDerivative stateDerivative : K)
    (hC : c ≠ 0) (hState : stateDerivative ≠ 0) :
    zeroCompletionVelocity (c * completionDerivative)
        (c * stateDerivative) =
      zeroCompletionVelocity completionDerivative stateDerivative := by
  unfold zeroCompletionVelocity
  field_simp [hC, hState]

/-- At a simple zero, vanishing completion velocity is equivalent to vanishing
completion-direction forcing. -/
theorem zero_completion_velocity_eq_zero_iff
    {completionDerivative stateDerivative : K}
    (hState : stateDerivative ≠ 0) :
    zeroCompletionVelocity completionDerivative stateDerivative = 0 ↔
      completionDerivative = 0 := by
  simp [zeroCompletionVelocity, hState]

/-- A nonzero forcing term yields a nonzero velocity at a simple zero. -/
theorem zero_completion_velocity_ne_zero
    {completionDerivative stateDerivative : K}
    (hCompletion : completionDerivative ≠ 0)
    (hState : stateDerivative ≠ 0) :
    zeroCompletionVelocity completionDerivative stateDerivative ≠ 0 := by
  exact (zero_completion_velocity_eq_zero_iff hState).not.mpr hCompletion

/-- At a singular state derivative, totalized division returns zero. This probe
carries no simple-zero velocity interpretation. -/
example (completionDerivative : K) :
    zeroCompletionVelocity completionDerivative 0 = 0 := by
  simp [zeroCompletionVelocity]

#print axioms zero_completion_velocity_eq_of_chain
#print axioms zero_completion_velocity_satisfies_chain
#print axioms zero_completion_velocity_scale_invariant
#print axioms zero_completion_velocity_eq_zero_iff
#print axioms zero_completion_velocity_ne_zero

end D5.S3.Analytic.ZetaCompletionFlow.SimpleZeroCompletionVelocity
