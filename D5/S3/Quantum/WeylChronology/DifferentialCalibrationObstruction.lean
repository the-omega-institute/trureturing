/- GID: D5/S3/Quantum/WeylChronology/DifferentialCalibrationObstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/WeylChronology/DifferentialCalibrationObstruction
   mirror-E: none(waiver:exact-control-identifiability)
   anchors: []
   utility: none
   digest: Radius-form consumers of the existing sharp closed-path ambiguity theorems. -/

import D5.S3.Quantum.WeylChronology.ClosedPathChronologyAmbiguity

/-!
# Differential calibration: radius-form consumers

The general sharp squared-budget results are owned by
`ClosedPathChronologyAmbiguity`. This module retains the already-published
radius-form API and uses that owner directly. The former duplicate Cauchy,
attainment, and collision proofs have been removed. These five statements are
bind-only companion consumers, not five additional mathematical discoveries.

The hidden object includes both the history and its realized error record.
The collision compares two admissible records at one fixed setting; it does
not assert a collision under every additional intervention or under a single
shared nuisance. The real-phase converse does not exclude periodic aliases.
For physical interpretation the radius is nonnegative; the algebraic API
uses its square and also permits negative real arguments.

Verification: source and mathematical review only. No Lean elaboration,
transitive axiom audit, Scribe emission or repository admission is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.WeylChronology.DifferentialCalibrationObstruction

open D5.S3.Quantum.WeylChronology.SymmetricGaussianCompensation
open D5.S3.Quantum.WeylChronology.ClosedPathChronologyAmbiguity
open D5.S3.Observer.GoldenChronology.GoldenMagnusParityRecovery

noncomputable section

/-- Radius-API companion of `closed_error_phase`. -/
theorem zero_total_error_phase (X Y ux uy : ℝ) :
    splitPhase X Y ux uy (-ux) (-uy) = Y * ux - X * uy :=
  closed_error_phase X Y ux uy

/-- Specialize the existing exact squared-budget theorem to `radius ^ 2`. -/
theorem zero_total_phase_radius_iff (X Y angle radius : ℝ)
    (hendpoint : 0 < X ^ 2 + Y ^ 2) :
    (∃ ux uy : ℝ, ux ^ 2 + uy ^ 2 ≤ radius ^ 2 ∧
      splitPhase X Y ux uy (-ux) (-uy) = angle) ↔
      angle ^ 2 ≤ radius ^ 2 * (X ^ 2 + Y ^ 2) := by
  simpa only [mul_comm] using
    bounded_closed_phase_iff X Y angle (radius ^ 2) hendpoint

/-- Radius-form companion of the sharp unwrapped collision theorem. -/
theorem two_record_phase_alias_iff (X Y phaseL phaseR radius : ℝ)
    (hendpoint : 0 < X ^ 2 + Y ^ 2) :
    (∃ ux uy vx vy : ℝ,
      ux ^ 2 + uy ^ 2 ≤ radius ^ 2 ∧
      vx ^ 2 + vy ^ 2 ≤ radius ^ 2 ∧
      phaseL + splitPhase X Y ux uy (-ux) (-uy) =
        phaseR + splitPhase X Y vx vy (-vx) (-vy)) ↔
      (phaseL - phaseR) ^ 2 ≤ 4 * radius ^ 2 * (X ^ 2 + Y ^ 2) := by
  have hsq : (phaseR - phaseL) ^ 2 = (phaseL - phaseR) ^ 2 := by ring
  simpa only [hsq, mul_assoc, mul_left_comm, mul_comm] using
    bounded_real_phase_collision_iff X Y phaseL phaseR (radius ^ 2) hendpoint

/-- Expand the phase in the existing literal completed-action normal form. -/
theorem zero_total_control_normal_form (a b ux uy : ℝ)
    (word : List Bool) (f : ℝ → ℂ) :
    splitCompensatedWord a b ux uy (-ux) (-uy) word f =
      Complex.exp (((a*b*(magnusCenter word : ℝ) +
        (b*(word.count false : ℝ))*ux - (a*(word.count true : ℝ))*uy : ℝ) : ℂ) *
          Complex.I) • f := by
  rw [closed_error_word_normal_form, closed_error_phase]
  have he : a*b*(magnusCenter word : ℝ) +
      ((b*(word.count false : ℝ))*ux - (a*(word.count true : ℝ))*uy) =
      a*b*(magnusCenter word : ℝ) + (b*(word.count false : ℝ))*ux -
        (a*(word.count true : ℝ))*uy := by ring
  rw [he]

/-- Apply the existing full-action collision with the radius convention. -/
theorem closed_endpoint_operator_alias
    (a b radius : ℝ) (left right : List Bool)
    (htrue : left.count true = right.count true)
    (hfalse : left.count false = right.count false)
    (hendpoint : 0 < (a*(left.count true : ℝ))^2 + (b*(left.count false : ℝ))^2)
    (hgap : (a*b*((magnusCenter left : ℝ)-(magnusCenter right : ℝ)))^2 ≤
      4*radius^2*((a*(left.count true : ℝ))^2+(b*(left.count false : ℝ))^2)) :
    ∃ ux uy vx vy : ℝ,
      ux^2+uy^2 ≤ radius^2 ∧ vx^2+vy^2 ≤ radius^2 ∧
      ∀ f : ℝ → ℂ,
        splitCompensatedWord a b ux uy (-ux) (-uy) left f =
        splitCompensatedWord a b vx vy (-vx) (-vy) right f := by
  have hsq : (a*b*((magnusCenter right : ℝ)-(magnusCenter left : ℝ)))^2 =
      (a*b*((magnusCenter left : ℝ)-(magnusCenter right : ℝ)))^2 := by ring
  have hbudget : (a*b*((magnusCenter right : ℝ)-(magnusCenter left : ℝ)))^2 ≤
      4*((a*(left.count true : ℝ))^2+(b*(left.count false : ℝ))^2)*radius^2 := by
    rw [hsq]
    nlinarith [hgap]
  exact same_inventory_bounded_action_collision a b (radius ^ 2) left right
    htrue hfalse hendpoint hbudget

#print axioms zero_total_phase_radius_iff
#print axioms two_record_phase_alias_iff
#print axioms closed_endpoint_operator_alias

end
end D5.S3.Quantum.WeylChronology.DifferentialCalibrationObstruction
