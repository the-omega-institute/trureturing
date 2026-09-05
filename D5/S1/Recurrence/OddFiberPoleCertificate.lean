/- GID: D5/S1/Recurrence/OddFiberPoleCertificate
   generality: G
   mirror-B: D5/B/S1/Recurrence/OddFiberPoleCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For odd fiber capacity, multiplying the row amplitude by v plus one removes its singular factor and gives a regularized polynomial whose value at minus one is exactly plus or minus one. -/

import Mathlib

/- Library-search audit trail (2026-09-04):
   * D5 keyword and generalized searches found
     `FiberCapacityDivisibility.one_add_x_dvd_fiber_polynomial_iff`, which
     already owns the even-capacity divisibility criterion and is not reproved.
     `AlternatingPoleCoefficients` treats coefficients of higher-order formal
     power-series poles, not this finite fiber's normalized value at minus one.
   * Pinned Mathlib supplies the exact identities `neg_one_geom_sum` and
     `geom_sum_mul_neg`; both are applied directly below. No whole simple-pole
     certificate for the displayed fiber amplitude was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.OddFiberPoleCertificate

open Finset

/-- For odd capacity, the apparent factor at `v = -1` is a genuine simple
pole certificate: away from `v = ±1`, multiplying the rational row amplitude
by `v + 1` gives the regularized finite geometric polynomial, and that
polynomial evaluates to `(-1)^start`, hence has absolute value one. -/
theorem odd_fiber_pole_certificate
    (start capacity : ℕ) (capacity_odd : Odd capacity) :
    let regularized : ℝ -> ℝ := fun v =>
      v ^ start * ∑ i ∈ range capacity, v ^ i
    let amplitude : ℝ -> ℝ := fun v =>
      v ^ start * (1 - v ^ capacity) / (1 - v ^ 2)
    regularized (-1) = (-1 : ℝ) ^ start ∧
      |regularized (-1)| = 1 ∧
      (forall v, v ≠ 1 -> v ≠ -1 ->
        (v + 1) * amplitude v = regularized v) := by
  dsimp
  have capacity_not_even : ¬ Even capacity :=
    Nat.not_even_iff_odd.mpr capacity_odd
  constructor
  · simp [neg_one_geom_sum, capacity_not_even]
  constructor
  · simp [neg_one_geom_sum, capacity_not_even]
  · intro v not_one not_neg_one
    have one_sub_ne : 1 - v ≠ 0 := sub_ne_zero.mpr (Ne.symm not_one)
    have one_add_ne : 1 + v ≠ 0 := by
      intro zero_sum
      apply not_neg_one
      linarith
    have denominator_factor : 1 - v ^ 2 = (1 - v) * (1 + v) := by
      ring
    calc
      (v + 1) * (v ^ start * (1 - v ^ capacity) / (1 - v ^ 2)) =
          v ^ start * ((v + 1) * (1 - v ^ capacity) /
            ((1 - v) * (1 + v))) := by rw [denominator_factor]; ring
      _ = v ^ start * ((1 - v ^ capacity) / (1 - v)) := by
        congr 1
        field_simp [one_sub_ne, one_add_ne]
        ring
      _ = v ^ start * ∑ i ∈ range capacity, v ^ i := by
        congr 1
        apply (div_eq_iff one_sub_ne).2
        exact (geom_sum_mul_neg v capacity).symm

#print axioms odd_fiber_pole_certificate

end D5.S1.Recurrence.OddFiberPoleCertificate
