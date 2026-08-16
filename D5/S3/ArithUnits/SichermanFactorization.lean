/- GID: D5/S3/ArithUnits/SichermanFactorization
   generality: G
   mirror-B: D5/B/S3/ArithUnits/SichermanFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An explicit polynomial has two distinct nonnegative-coefficient factorizations. -/

import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring

namespace D5.S3.ArithUnits.SichermanFactorization

open Polynomial

/-- The same polynomial over `ℕ` has two distinct ordered factorization pairs.

This closes only the explicit polynomial identity in the source atom. It does not claim a general
failure of unique factorization for `ℕ[X]` or classify all spectral factorizations.
-/
theorem sicherman_polynomial_has_distinct_factorizations :
    let X : Polynomial ℕ := Polynomial.X
    (1 + X) * (1 + X ^ 2 + X ^ 4) =
        (1 + X + X ^ 2) * (1 + X ^ 3) ∧
      (1 + X, 1 + X ^ 2 + X ^ 4) ≠
        (1 + X + X ^ 2, 1 + X ^ 3) := by
  dsimp only
  constructor
  · ring
  · intro h
    have hcoeff := congrArg (fun p : Polynomial ℕ × Polynomial ℕ => p.1.coeff 2) h
    norm_num [coeff_add, coeff_one, coeff_X_pow] at hcoeff

#print axioms sicherman_polynomial_has_distinct_factorizations

end D5.S3.ArithUnits.SichermanFactorization
