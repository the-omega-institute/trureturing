/- GID: D5/S1/Solenoid/HiddenMotionRigidity
   generality: I
   mirror-B: D5/B/S1/Solenoid/HiddenMotionRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every continuous path in the prime-adic hidden fiber is constant. -/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.UnitInterval

namespace D5.S1.Solenoid.HiddenMotionRigidity

/-- A bundled prime supplies the primality fact required by its ring of
`p`-adic integers. -/
private instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- A continuous motion from the unit interval into the prime-adic hidden fiber
is constant. This is a thin specialization of mathlib's theorem that every
continuous map from a preconnected space to a totally disconnected space is
constant. -/
theorem prime_adic_hidden_motion_rigidity
    (hiddenMotion : unitInterval → ∀ p : Nat.Primes, ℤ_[p.1])
    (hContinuous : Continuous hiddenMotion) :
    ∀ x y, hiddenMotion x = hiddenMotion y :=
  TotallyDisconnectedSpace.eq_of_continuous hiddenMotion hContinuous

/-- Forcing check for the codomain hypothesis: after replacing the totally
disconnected hidden fiber by `ℝ`, the identity inclusion of the unit interval
is continuous and genuinely nonconstant. -/
theorem real_unit_interval_has_nonconstant_continuous_motion :
    ∃ (motion : unitInterval → ℝ), Continuous motion ∧
      ∃ x y, motion x ≠ motion y := by
  refine ⟨Subtype.val, continuous_subtype_val, 0, 1, ?_⟩
  norm_num

end D5.S1.Solenoid.HiddenMotionRigidity
