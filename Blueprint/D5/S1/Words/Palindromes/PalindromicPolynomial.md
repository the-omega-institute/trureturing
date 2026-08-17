# Palindromic Polynomials Are Self-Reciprocal

## Abstract

Palindromic coefficients make a polynomial equal to its coefficient reversal.

This document closes only the structural implication from palindromic truncation to self-reciprocity in residual observation 6.156. It does not formalize the experimental zero locations, geometric accumulation, or root-on-circle preference stated nearby.

**Theorem 1.1 (Palindromic coefficients give self-reciprocity).**

$$\forall R, \operatorname{Semiring}(R), \forall p\in\operatorname{Polynomial}(R), (\forall i, i \le \operatorname{natDegree}\left(p\right) \Rightarrow \operatorname{coeff}\left(p, i\right) = \operatorname{coeff}\left(p, \operatorname{natDegree}\left(p\right) - i\right)) \Rightarrow \operatorname{reverse}\left(p\right) = p$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PalindromicPolynomial.reverse_eq_self_of_palindromic_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Polynomial extensionality reduces the claim to coefficients. Mathlib's coefficient formula for polynomial reversal changes an in-range index i to natDegree(p) minus i; the palindrome hypothesis closes that case, while reversal fixes indices above the degree.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PalindromicPolynomial.reverse_eq_self_of_palindromic_coefficients`
