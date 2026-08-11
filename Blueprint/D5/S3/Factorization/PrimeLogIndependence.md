# Integer Linear Independence of Prime Logarithms

## Abstract

The logarithms of the primes are linearly independent over the integers.

**Theorem 1.1 (Prime logarithms are integer-linearly independent).**

$$\forall S,k, (\forall p \in S, \operatorname{Prime}(p)) \Rightarrow\\\sum_{p \in S} k(p) \log p=0 \Rightarrow\\\forall p \in S, k(p)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimeLogIndependence.prime_log_indep` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite set S of prime numbers and integer coefficients k, if the weighted sum of the logarithms log p over S vanishes, then every coefficient k p is zero. Equivalently, the logarithms of distinct primes are linearly independent over the integers, hence over the rationals.

The proof splits S into the primes with nonnegative coefficient and those with negative coefficient. Exponentiating the vanishing sum turns it into an equality of two prime-power products, one over each part; these are products over disjoint sets of primes, so reading the prime-power factorization at any prime in either part forces that exponent, and therefore that coefficient, to vanish. The decisive step is the uniqueness of prime factorization.

This is not a restatement of a library lemma: a search of Mathlib finds the prime-factorization multiplication and power laws and the exponential of a sum, but no linear independence of prime logarithms. The statement is the arithmetic core behind the dense winding of the zeta phase line on the torus of per-axis phases; only that independence is claimed here, not the topological density it implies.

## References

- Truth anchor: `D5/S3/Factorization/PrimeLogIndependence.prime_log_indep`
