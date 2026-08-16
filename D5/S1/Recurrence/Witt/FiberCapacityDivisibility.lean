/- GID: D5/S1/Recurrence/Witt/FiberCapacityDivisibility
   generality: G
   mirror-B: D5/B/S1/Recurrence/Witt/FiberCapacityDivisibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A fiber polynomial has the factor X plus one exactly at even capacity. -/

import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Ring.GeomSum

namespace D5.S1.Recurrence.Witt.FiberCapacityDivisibility

open Finset Polynomial

/-- The polynomial of a consecutive fiber with the given starting exponent and capacity. -/
noncomputable def fiberPolynomial (start capacity : Nat) : Polynomial Int :=
  X ^ start * ∑ i ∈ range capacity, X ^ i

/-- A consecutive fiber polynomial is divisible by `1 + X` exactly when its capacity is even. -/
theorem one_add_x_dvd_fiber_polynomial_iff (start capacity : Nat) :
    (1 + X : Polynomial Int) ∣ fiberPolynomial start capacity ↔ Even capacity := by
  rw [show (1 + X : Polynomial Int) = X - C (-1) by simp [sub_eq_add_neg, add_comm],
    Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, fiberPolynomial, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_geom_sum, neg_one_geom_sum]
  by_cases hcapacity : Even capacity <;> simp [hcapacity]

end D5.S1.Recurrence.Witt.FiberCapacityDivisibility
