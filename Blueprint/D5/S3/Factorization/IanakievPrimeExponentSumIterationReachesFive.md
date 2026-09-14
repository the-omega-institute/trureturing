# Ianakiev's A008474 Iteration Conjecture

## Abstract

Every prime-exponent sum orbit starting above four reaches five.

**Definition 1.1 (The prime-exponent sum).**

$$\forall n \in {\mathbb N},\; F\left(n\right) = \sum_{p \in primeFactors\left(n\right)} (p + factorization\left(n, p\right))$$

*Formalization.* `D5/S3/Factorization/IanakievPrimeExponentSumIterationReachesFive.F` (`✓ std3`).

*Citation.* Ivan N. Ianakiev; Olivier Gérard (2014). *OEIS A008474, If n = Product (p_j^k_j) then a(n) = Sum (p_j + k_j)*. URL: <https://oeis.org/A008474>.

*Commentary.*

For every natural n, F(n) sums p plus the exponent of p over the distinct prime divisors of n. The empty prime-factor sets at zero and one give F(0)=F(1)=0.

**Theorem 1.2 (Every orbit above four reaches five).**

$$\forall m \in {\mathbb N},\; 4 < m \Rightarrow \left(\exists t \in {\mathbb N},\; \left(F^{[t]}\right)\left(m\right) = 5\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/IanakievPrimeExponentSumIterationReachesFive.ianakiev_a008474` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a008474-prime-exponent-sum-iteration-reaches-five` (proved) by `D5/S3/Factorization/IanakievPrimeExponentSumIterationReachesFive.ianakiev_a008474`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a008474-prime-exponent-sum-iteration-reaches-five","declaration_gid":"D5/S3/Factorization/IanakievPrimeExponentSumIterationReachesFive.ianakiev_a008474","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

For every natural m greater than four, some finite iterate of F equals five. The displayed superscript [t] denotes Function.iterate (Nat.iterate). Composite inputs descend in one step and sufficiently large prime inputs descend in two steps. The remaining values enter the cycle 5 -> 6 -> 7 -> 8 -> 5. Since four is fixed, the lower bound is sharp. No generating-function identity is asserted.

## References

- Truth anchor: `D5/S3/Factorization/IanakievPrimeExponentSumIterationReachesFive.F`
- Truth anchor: `D5/S3/Factorization/IanakievPrimeExponentSumIterationReachesFive.ianakiev_a008474`
