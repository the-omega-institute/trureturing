/- GID: D5/S1/Words/Palindromes/PalindromicPolynomial
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PalindromicPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Palindromic coefficients make a polynomial equal to its coefficient reversal. -/

import Mathlib.Algebra.Polynomial.Reverse

open scoped Polynomial

namespace D5.S1.Words

/-- A polynomial whose coefficients are palindromic through its degree is self-reciprocal. -/
theorem reverse_eq_self_of_palindromic_coefficients {R : Type*} [Semiring R]
    (p : R[X])
    (hpal : ∀ i, i ≤ p.natDegree → p.coeff i = p.coeff (p.natDegree - i)) :
    p.reverse = p := by
  ext i
  rw [Polynomial.coeff_reverse]
  by_cases hi : i ≤ p.natDegree
  · rw [Polynomial.revAt_le hi]
    exact (hpal i hi).symm
  · rw [Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hi)]

#print axioms reverse_eq_self_of_palindromic_coefficients

end D5.S1.Words
