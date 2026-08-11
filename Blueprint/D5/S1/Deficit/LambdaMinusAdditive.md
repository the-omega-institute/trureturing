# Additivity of the Contraction Reading over Coprimes

## Abstract

The contraction reading is additive over coprime factors.

**Theorem 1.1 (The contraction reading is additive over coprime factors).**

$$\forall m,n,\quad\gcd(m,n)=1 \implies \operatorname{lambdaMinus}(mn)=\operatorname{lambdaMinus}(m)+\operatorname{lambdaMinus}(n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/LambdaMinusAdditive.lambdaMinus_coprime_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For coprime natural numbers m and n, the contraction reading of their product equals the sum of their separate readings exactly, with no error term. The reading is defined as a finite sum over prime exponents, and coprimality means m and n share no prime, so the two prime supports are disjoint and the sum over the product splits cleanly into the two separate sums.

The proof rewrites the factorization of the product as the sum of the two factorizations and observes that the prime supports are disjoint, because coprime numbers have disjoint prime factors. A finitely-supported sum over a disjoint union of supports distributes as the sum of the two restricted sums, which are exactly the readings of m and of n.

This is the exact companion of the almost-additivity bound: that result controls the failure of additivity by the logarithm of the product of the common primes, and here, when there are no common primes, that bound is zero and additivity holds on the nose. Mathlib supplies the prime-factorization multiplication law, the coprime disjoint-prime-factors identity, and the disjoint-support sum-splitting lemma; the repository supplies the contraction reading. Searches found no library declaration for the assembled coprime-additivity statement.

## References

- Truth anchor: `D5/S1/Deficit/LambdaMinusAdditive.lambdaMinus_coprime_add`
- Dependency: [D5/S1/Deficit/AlmostAdditivity](AlmostAdditivity.md)
