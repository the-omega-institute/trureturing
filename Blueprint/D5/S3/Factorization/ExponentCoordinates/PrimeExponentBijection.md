# Prime-Exponent Bijection

## Abstract

Positive naturals are exactly the finite prime-supported exponent families.

**Definition 1.1 (Finite prime-power product).**

$$primeExponentProduct: PrimeExponentTable \Rightarrow \mathbb{N}_{>0}$$

*Formalization.* `D5/S3/Factorization/ExponentCoordinates/PrimeExponentBijection.primeExponentProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A prime-supported exponent family reconstructs a positive natural by the finite product of each prime raised to its stored exponent.

**Definition 1.2 (Prime-exponent language equivalence).**

$$primeExponentLanguageEquiv: \mathbb{N}_{>0} \sim PrimeExponentTable$$

*Formalization.* `D5/S3/Factorization/ExponentCoordinates/PrimeExponentBijection.primeExponentLanguageEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The equivalence is Mathlib's factorization equivalence, with the existing repository prime-exponent language as its forward value.

**Theorem 1.3 (The equivalence uses the existing prime-exponent language).**

$$\forall n, \operatorname{primeExponentLanguageEquiv}\left(n\right) = \operatorname{primeExponentLanguage}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/ExponentCoordinates/PrimeExponentBijection.prime_exponent_language_equiv_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural, the forward value of the equivalence is exactly the previously defined primeExponentLanguage readout.

**Theorem 1.4 (The inverse is the finite product of prime powers).**

$$\forall e, \operatorname{primeExponentProduct}\left(e\right) = \prod_{p} p^{\operatorname{e}\left(p\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/ExponentCoordinates/PrimeExponentBijection.prime_exponent_product_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The underlying natural of the named inverse is the finite Finsupp product of p to the exponent e(p).

**Theorem 1.5 (Prime-exponent language is bijective on prime support).**

$$\operatorname{Bijective}(primeExponentLanguageEquiv)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/ExponentCoordinates/PrimeExponentBijection.prime_exponent_language_bijection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Injectivity is reused from prime_exponent_language_complete. Surjectivity comes directly from Nat.factorizationEquiv; no factorization theorem is reproved.

**Theorem 1.6 (Positivity is necessary).**

$$\neg\operatorname{Injective}(factorization:\mathbb{N} \Rightarrow Finsupp)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/ExponentCoordinates/PrimeExponentBijection.positivity_restriction_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On all naturals, zero and one both have the empty factorization, so the raw factorization function is not injective.

**Theorem 1.7 (Prime support is necessary).**

$$\neg\operatorname{Surjective}(primeExponentLanguage:\mathbb{N}_{>0} \Rightarrow Finsupp)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/ExponentCoordinates/PrimeExponentBijection.prime_support_restriction_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unrestricted Finsupp codomain contains a family with exponent one at the composite four. Every natural factorization is zero there, so that family has no preimage. PrimeExponentTable excludes it by type.

## References

- Truth anchor: `D5/S3/Factorization/ExponentCoordinates/PrimeExponentBijection.positivity_restriction_is_necessary`
- Truth anchor: `D5/S3/Factorization/ExponentCoordinates/PrimeExponentBijection.primeExponentLanguageEquiv`
- Truth anchor: `D5/S3/Factorization/ExponentCoordinates/PrimeExponentBijection.primeExponentProduct`
- Truth anchor: `D5/S3/Factorization/ExponentCoordinates/PrimeExponentBijection.prime_exponent_language_bijection`
- Truth anchor: `D5/S3/Factorization/ExponentCoordinates/PrimeExponentBijection.prime_exponent_language_equiv_apply`
- Truth anchor: `D5/S3/Factorization/ExponentCoordinates/PrimeExponentBijection.prime_exponent_product_formula`
- Truth anchor: `D5/S3/Factorization/ExponentCoordinates/PrimeExponentBijection.prime_support_restriction_is_necessary`
- Dependency: [D5/S1/Digit/PrimeAxisEncoding](../../../S1/Digit/PrimeAxisEncoding.md)
- Dependency: [D5/S3/Factorization/PrimePowers/PrimeExponentLanguageComplete](../PrimePowers/PrimeExponentLanguageComplete.md)
