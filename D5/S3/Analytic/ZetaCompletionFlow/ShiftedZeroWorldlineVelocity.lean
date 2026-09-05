/- GID: D5/S3/Analytic/ZetaCompletionFlow/ShiftedZeroWorldlineVelocity
   generality: I
   mirror-B: D5/B/S3/Analytic/ZetaCompletionFlow/ShiftedZeroWorldlineVelocity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A shifted affine zero has a fixed horizontal label and crossing parameter, with universal velocity minus i. -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/- Duplicate-search audit (2026-09-05):
   * Exact and spelling-variant D5 searches covered shifted zeros, affine root
     motion, completion velocity, worldlines, horizontal labels, and boundary
     crossing times; no theorem states this concrete trajectory.
   * The digestion index leaves the source atom residual-open. The retired
     formalization-receipt directory is absent and was not inspected.
   * Generalized searches found the frozen generic affine displacement,
     finite-difference Newton predictor, and simple-zero chain rule, but none
     derives the concrete root, coordinates, crossing time, and velocity here.
   * The source atom is absent from the in-flight atom index, and neither the
     proposed module nor an equivalent worldline occurs in the in-flight module
     index, remote lane commit messages, or sibling worktrees.
   * Pinned Mathlib supplies complex-coordinate simplification,
     `Complex.ofReal_ne_zero`, and field algebra, but no packaged shifted-zero
     worldline theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ZetaCompletionFlow.ShiftedZeroWorldlineVelocity

/-- The shifted zero labelled by horizontal coordinate `-gamma` and boundary
crossing time `delta`, observed at depth `omega`. -/
def shiftedZeroWorldline (gamma delta omega : Real) : Complex :=
  (-gamma : Complex) + Complex.I * ((delta - omega : Real) : Complex)

/-- The affine observation equation whose zero is the shifted worldline. -/
def shiftedObservation
    (gamma delta omega : Real) (z : Complex) : Complex :=
  z - shiftedZeroWorldline gamma delta omega

/-- **Universal shifted-zero velocity.** The affine observation equation has
the displayed worldline as its unique zero at every depth.  Every nonzero
finite-difference quotient is exactly `-i`, independently of `gamma`, `delta`,
and the observation depth.  The real coordinate is the horizontal label
`-gamma`, while the imaginary coordinate is `delta - omega`, so boundary
crossing occurs exactly at `omega = delta`. -/
theorem shifted_zero_worldline_universal_velocity
    (gamma delta omega step : Real) (hStep : step ≠ 0) :
    (∀ t z,
      shiftedObservation gamma delta t z = 0 ↔
        z = shiftedZeroWorldline gamma delta t) ∧
    ((shiftedZeroWorldline gamma delta (omega + step) -
        shiftedZeroWorldline gamma delta omega) / (step : Complex) =
      -Complex.I) ∧
    (∀ t,
      (shiftedZeroWorldline gamma delta t).re = -gamma ∧
      (shiftedZeroWorldline gamma delta t).im = delta - t) ∧
    (∀ t,
      (shiftedZeroWorldline gamma delta t).im = 0 ↔ t = delta) := by
  fail_if_success rfl
  refine And.intro ?_ <| And.intro ?_ <| And.intro ?_ ?_
  · intro t z
    exact sub_eq_zero
  · have hStepComplex : (step : Complex) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hStep
    apply (div_eq_iff hStepComplex).2
    simp only [shiftedZeroWorldline]
    push_cast
    ring
  · intro t
    constructor <;> simp [shiftedZeroWorldline]
  · intro t
    simp only [shiftedZeroWorldline, Complex.add_im, Complex.neg_im,
      Complex.ofReal_im, neg_zero, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add]
    rw [sub_eq_zero, eq_comm]

#print axioms shifted_zero_worldline_universal_velocity

end D5.S3.Analytic.ZetaCompletionFlow.ShiftedZeroWorldlineVelocity
