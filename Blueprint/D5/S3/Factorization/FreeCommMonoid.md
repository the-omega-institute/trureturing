# The Free Commutative Monoid on the Prime Axes

## Abstract

Positive naturals under multiplication form the free commutative monoid on the primes.

**Theorem 1.1 (Prime factorization is an isomorphism onto the free monoid on the primes).**

$$\forall m,n\in \mathbb{N}_{+},\ \operatorname{v}_{p}(mn)=\operatorname{v}_{p}(m)+\operatorname{v}_{p}(n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/FreeCommMonoid.pnat_free_comm_monoid_on_primes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The deposited statement packages the freeness reading of unique factorization in four clauses. First, the prime-factorization map from the positive naturals under multiplication to the multiset monoid over the primes, written multiplicatively, is bijective. Second, it is multiplicative, so it is a monoid isomorphism. Third, the target has the universal property of the free commutative monoid on the primes: every prime-indexed family in any commutative monoid extends to a unique monoid homomorphism out of the multiset monoid. Fourth, the prime-exponent readouts are additive: on each prime axis the exponent of a product is the sum of the exponents of the factors, with no nonzeroness side condition because positive naturals never vanish.

The isomorphism clauses are a thin honest upgrade of pinned mathlib: the underlying equivalence is the prime multiset equivalence, its multiplicativity is the factor-multiset product law, and the exponent additivity is the factorization product law read on positive naturals. The universal-property clause is proved natively: the extension maps a multiset of primes through the family and takes the product, and uniqueness is multiset induction against the two homomorphism laws. Pinned mathlib has no named free-commutative-monoid universal-property interface, so that clause is new glue rather than a citation.

This is the freeness half of the prime-axis coordinate reading: multiplication of positive naturals is coordinatewise addition of prime exponents, so the primes are free axes and no relation ever couples two axes. No claim is made here about unique factorization in general monoids, about the golden or Zeckendorf digit encodings of the exponents, or about any ordering or density structure on the primes.

## References

- Truth anchor: `D5/S3/Factorization/FreeCommMonoid.pnat_free_comm_monoid_on_primes`
