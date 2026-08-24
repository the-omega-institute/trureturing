# Completeness of the Prime-Exponent Language

## Abstract

The complete prime-exponent readout separates positive natural numbers and has singleton fibers.

**Theorem 1.1 (The full prime-exponent language is complete on positive naturals).**

$$\operatorname{Injective}(primeExponentLanguage) \land \forall n \in \mathbb{N}_{>0}, \{m \in \mathbb{N}_{>0} \mid \operatorname{primeExponentLanguage}\left(m\right) = \operatorname{primeExponentLanguage}\left(n\right)\} = \{n\}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/PrimeExponentLanguageComplete.prime_exponent_language_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The readout assigns to each positive natural number its full finitely supported family of prime exponents. Distinct positive naturals have distinct readouts, so the map loses no arithmetic information.

Equivalently, fixing any positive natural n leaves exactly one input with the same exponent data: n itself. The positivity restriction is essential because the unrestricted natural-number factorizations of zero and one are both the empty exponent family.

The proof invokes the injectivity of Mathlib's factorization equivalence and then applies that injectivity pointwise to identify each readout fiber with its singleton.

## References

- Truth anchor: `D5/S3/Factorization/PrimePowers/PrimeExponentLanguageComplete.prime_exponent_language_complete`
