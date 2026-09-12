# Finite Euler products for divisor sums

## Abstract

Complex divisor sums factor into finite geometric products for every exponent.

The variables n, d, p and j are natural numbers, and s is complex. The set divisors(n) contains the positive divisors and is empty for n=0. The set primeFactors(n) contains distinct prime divisors; factorization(n,p) is the multiplicity of p. Complex powers use the principal logarithm.

**Definition 1.1 (The divisor Dirichlet polynomial).**

$$\operatorname{Z}\left(n, s\right) = \sum_{d \in \operatorname{divisors}\left(n\right)} {d}^{-s}$$

*Formalization.* `D5/S3/Arith/DivisorGibbs/FiniteDivisorEulerProduct.Z` (`✓ std3`).

*Citation.* Mathlib contributors (2026). *Multiplicative arithmetic functions and finite divisor sums in Mathlib*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean>.

*Commentary.*

Sum over the actual divisors of n. This definition also assigns zero at n=0.

**Theorem 1.2 (Finite Euler factorization).**

$$\forall n \in \mathbb{N}, s \in \mathbb{C}, 0 < n \Rightarrow \operatorname{Z}\left(n, s\right) = \prod_{p \in \operatorname{primeFactors}\left(n\right)} \sum_{j=0}^{\operatorname{factorization}\left(n, p\right)} {{p}^{-s}}^{j}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DivisorGibbs/FiniteDivisorEulerProduct.divisor_sum_eq_euler_product` (`✓ std3`). ∎

*Citation.* Mathlib contributors (2026). *Multiplicative arithmetic functions and finite divisor sums in Mathlib*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean>.

*Commentary.*

Convolving the multiplicative complex power function with the arithmetic zeta function gives the divisor sum. Multiplicative factorization reduces it to prime powers, whose divisors are the powers from zero through the prime multiplicity. The power function is assigned zero at the natural index zero for this convolution; that index is never a positive divisor. No restriction on s is needed: at s=0 every local summand equals one.

**Theorem 1.3 (Zero outside the divisor set).**

$$\forall n \in \mathbb{N}, s \in \mathbb{C}, \operatorname{Z}\left(n, s\right) = \sum_{d \in \mathbb{N}} \operatorname{indicator}\left(\operatorname{divisors}\left(n\right), d\right) {d}^{-s}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DivisorGibbs/FiniteDivisorEulerProduct.divisor_sum_eq_tsum` (`✓ std3`). ∎

*Citation.* Mathlib contributors (2026). *Multiplicative arithmetic functions and finite divisor sums in Mathlib*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean>.

*Commentary.*

Here indicator(A,d) is one on A and zero off A. The displayed natural-indexed sum is the infinite sum tsum. Its summands vanish outside the finite divisor set, so it equals the finite sum without any convergence condition on s. This includes n=0 and s=0.

## References

- Truth anchor: `D5/S3/Arith/DivisorGibbs/FiniteDivisorEulerProduct.Z`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/FiniteDivisorEulerProduct.divisor_sum_eq_euler_product`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/FiniteDivisorEulerProduct.divisor_sum_eq_tsum`
