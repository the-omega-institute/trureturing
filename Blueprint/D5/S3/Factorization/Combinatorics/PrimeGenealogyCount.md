# Ordered Prime-Factor Genealogies

## Abstract

The number of ordered prime-factor genealogies is the multinomial of the prime multiplicities.

**Theorem 1.1 (Prime-factor orderings have the multinomial count).**

$$\forall n \in \mathbb{N},\ c(n) = \frac{(\sum_{p} a_{p})!}{\prod_{p} a_{p}!}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Combinatorics/PrimeGenealogyCount.prime_genealogy_count_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a natural number n, let a_p be the exponent of p in the canonical prime factorization of n. An ordered prime-factor genealogy is a distinct ordering of that prime-factor multiset. Its count is the factorial of the total multiplicity, sum_p a_p, divided by the product of the individual factorials, product_p a_p!. The formula also covers zero and one under Mathlib's canonical prime-factor-list convention.

The Lean proof does not reconstruct the permutation count. Pinned Mathlib already defines Multiset.countPerms through Finsupp.multinomial and proves that the factorization of n is the frequency table of its canonical prime factor list. The deposited theorem only rewrites those two upstream truths into the factorial quotient at this repository address.

This closes only the explicit multinomial count formula in the source atom. The recurrence over prime divisors, the maximal-chain interpretation, the prime-zeta generating series, its growth exponent, and the numerical asymptotic constant remain outside this claim.

## References

- Truth anchor: `D5/S3/Factorization/Combinatorics/PrimeGenealogyCount.prime_genealogy_count_formula`
