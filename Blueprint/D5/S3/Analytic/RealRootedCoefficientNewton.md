# Newton inequalities from the upstream symmetric-function proof

## Abstract

Newton inequalities for elementary symmetric functions of real multisets.

**Theorem 1.1 (The reduced Newton inequality).**

Lean statement: `D5/S3/Analytic/RealRootedCoefficientNewton.esymm_mul_esymm_le_sq_esymm`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/RealRootedCoefficientNewton.esymm_mul_esymm_le_sq_esymm` (`✓ std3`). ∎

*Citation.* Terence Tao (2026). *The Newton and Maclaurin inequalities for symmetric polynomials*. URL: <https://github.com/leanprover-community/mathlib4/blob/e3c1793d0e097d9b8d782a323e91c99c2ef0d64c/Mathlib/Analysis/MeanInequalitiesSymmetric.lean>.

*Commentary.*

For a multiset s of N real numbers and every natural k, the product (k+2)(N-k)e_k e_(k+2) is at most (k+1)(N-k-1)e_(k+1)^2, where e_j is its j-th elementary symmetric function. No sign or distinctness assumption is imposed on the entries, and indices beyond N are included.

The upstream proof represents elementary symmetric functions by a product of linear factors. The derivative has real roots with multiplicities; normalizing its leading coefficient reduces the number of entries while preserving normalized symmetric functions. Strong induction, the second-degree sum-of-squares inequality, and inversion at the last index prove Newton's inequality. In the Crown theorem, Vieta's formula for the negated root multiset converts this result to the needed coefficient inequalities. The license note identifies the immutable source and preserves its complete Apache license.

## References

- Truth anchor: `D5/S3/Analytic/RealRootedCoefficientNewton.esymm_mul_esymm_le_sq_esymm`
