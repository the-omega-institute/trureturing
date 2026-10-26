/- GID: D5/S3/Quantum/QuantumChannels/NonUnitalNetworkConditionImplication
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/NonUnitalNetworkConditionImplication
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Non-unital channel constraints imply both network nonlocality-breaking bounds. -/

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.RingNF

/-! The channel parameter constraints imply both network nonlocality-breaking bounds. -/

namespace D5.S3.Quantum.QuantumChannels.NonUnitalNetworkConditionImplication

/-- The three channel constraints imply both network nonlocality-breaking bounds. -/
def claim : Prop :=
  ∀ t l1 l3 : ℝ,
    |l1| ≤ 1 →
    |l3| + |t| ≤ 1 →
    l1 ^ 2 + t ^ 2 ≤ (1 - |l3|) ^ 2 →
    (|t| + |l3|) ^ 2 + l1 ^ 2 ≤ 1 ∧
      2 * t ^ 2 * l1 ^ 2 + l1 ^ 4 + (|t| + |l3|) ^ 4 ≤ 1

theorem result : claim := by
  intro t l1 l3 _h1 hu hcap
  let A := l1 ^ 2
  let x := |l3|
  let y := |t|
  let u := x + y
  let D := (1 - x) ^ 2 - y ^ 2 - A
  have hA : 0 ≤ A := sq_nonneg l1
  have hx : 0 ≤ x := abs_nonneg l3
  have hy : 0 ≤ y := abs_nonneg t
  have hu1 : u ≤ 1 := hu
  have hD : 0 ≤ D := by
    dsimp [D, A, x, y]
    nlinarith only [hcap, sq_abs t]
  have hidentity1 : 1 - (A + u ^ 2) = D + 2 * x * (1 - u) := by
    dsimp [D, u]
    ring
  have hbound : A + u ^ 2 ≤ 1 := by
    nlinarith only [hD, hidentity1, mul_nonneg hx (sub_nonneg.mpr hu1)]
  have hnonneg : 0 ≤ A + u ^ 2 := add_nonneg hA (sq_nonneg u)
  have hidentity2 :
      (A + u ^ 2) ^ 2 - (A ^ 2 + 2 * y ^ 2 * A + u ^ 4) =
        2 * A * x * (x + 2 * y) := by
    dsimp [u]
    ring
  have hprod : 0 ≤ 2 * A * x * (x + 2 * y) := by positivity
  have hquartic : A ^ 2 + 2 * y ^ 2 * A + u ^ 4 ≤ 1 := by
    nlinarith only [hidentity2, hprod, (sq_le_one_iff₀ hnonneg).2 hbound]
  constructor
  · change (y + x) ^ 2 + A ≤ 1
    nlinarith only [hbound]
  · dsimp [A, u, x, y] at hquartic
    rw [sq_abs t] at hquartic
    nlinarith only [hquartic]

end D5.S3.Quantum.QuantumChannels.NonUnitalNetworkConditionImplication
