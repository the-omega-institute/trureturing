/- GID: D5/S3/Constants/Characterizations/ConnectionCoefficientComposition
   generality: G
   mirror-B: D5/B/S3/Constants/Characterizations/ConnectionCoefficientComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Connection coefficients compose, with the positive-real Ramanujan factorization. -/

import Mathlib

/- Library-search audit trail (2026-08-28):
   * Current-tree searches for connection/composite structural constants and
     the displayed square-root factorization found no exact D5 theorem.
   * Pinned Mathlib's exact `smul_smul` is applied to the abstract connection
     law. The commutative scalar carrier converts the action-order product
     `b * a` to the source-order product `a * b`.
   * Pinned Mathlib's exact `Real.sqrt_div`, `Real.sqrt_mul`, `Real.exp_half`,
     `Real.rpow_neg`, and `Real.sqrt_eq_rpow` are applied directly to the
     positive-real certificate. Local Mathlib grep found no theorem packaging
     both public clauses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.Characterizations.ConnectionCoefficientComposition

/-- Two successive scalar connection steps have product coefficient. On the
positive-real carrier, the displayed Ramanujan factor is correspondingly the
product of its Gaussian, exponential-flow, and scale terms. -/
theorem connection_coefficient_composition :
    (∀ (R M : Type) [CommSemiring R] [AddCommMonoid M] [Module R M]
      (a b : R) (X Y Z : M),
        Y = a • X → Z = b • Y → Z = (a * b) • X) ∧
      (∀ x : Real, 0 < x →
        Real.sqrt (Real.pi * Real.exp x / (2 * x)) =
          Real.sqrt (Real.pi / 2) * Real.exp (x / 2) *
            x ^ (-(1 : Real) / 2)) := by
  constructor
  · intro R M _ _ _ a b X Y Z hY hZ
    calc
      Z = b • Y := hZ
      _ = b • (a • X) := by rw [hY]
      _ = (b * a) • X := smul_smul b a X
      _ = (a * b) • X := by rw [mul_comm]
  · intro x hx
    have hsqrtTwo : Real.sqrt (2 : Real) ≠ 0 :=
      Real.sqrt_ne_zero'.2 (by norm_num)
    have hsqrtX : Real.sqrt x ≠ 0 := Real.sqrt_ne_zero'.2 hx
    rw [Real.sqrt_div (mul_nonneg Real.pi_pos.le (Real.exp_pos x).le),
      Real.sqrt_mul Real.pi_pos.le, ← Real.exp_half,
      Real.sqrt_mul (by norm_num : (0 : Real) ≤ 2),
      Real.sqrt_div Real.pi_pos.le,
      show (-(1 : Real) / 2) = -(1 / 2 : Real) by ring,
      Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
    field_simp

/- The first clause cannot be obtained from either input equality alone: both
successive path equations are needed to determine the composite endpoint. -/
example (a b X Y Z : Real) (hY : Y = a * X) (hZ : Z = b * Y) :
    Z = (a * b) * X := by
  simpa only [smul_eq_mul] using
    connection_coefficient_composition.1 Real Real a b X Y Z hY hZ

#print axioms connection_coefficient_composition

end D5.S3.Constants.Characterizations.ConnectionCoefficientComposition
