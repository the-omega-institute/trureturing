/- GID: D5/S3/AnalyticClosure/GeometricNumeratorParity
   generality: I
   mirror-B: D5/B/S3/AnalyticClosure/GeometricNumeratorParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A geometric numerator cancels the quadratic pole exactly at even capacities. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.GeomSum

/- Library-search audit trail (2026-08-16):
   * No equivalent statement was found in D5.
   * Pinned mathlib supplies `dvd_pow_sub_one_of_dvd`, `Polynomial.eval_dvd`,
     and `neg_one_pow_eq_one_iff_even`; no exact biconditional was found.
   * An external GitHub/Loogle-domain search through NyxID/Tavily found no exact hit. -/

namespace D5.S3.AnalyticClosure.GeometricNumeratorParity

open Polynomial

/-- The geometric numerator `X^cap - 1` cancels the quadratic denominator
`X^2 - 1` exactly when the capacity is even. -/
theorem geometric_numerator_divisible_iff_even (cap : ℕ) :
    (X ^ 2 - 1 : ℤ[X]) ∣ X ^ cap - 1 ↔ Even cap := by
  constructor
  · intro hdvd
    have hEval : (0 : ℤ) ∣ (-1 : ℤ) ^ cap - 1 := by
      simpa using Polynomial.eval_dvd (x := (-1 : ℤ)) hdvd
    have hpow : (-1 : ℤ) ^ cap = 1 := sub_eq_zero.mp (zero_dvd_iff.mp hEval)
    exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤ) ≠ 1)).mp hpow
  · intro hEven
    exact dvd_pow_sub_one_of_dvd hEven.two_dvd

#print axioms geometric_numerator_divisible_iff_even

end D5.S3.AnalyticClosure.GeometricNumeratorParity
