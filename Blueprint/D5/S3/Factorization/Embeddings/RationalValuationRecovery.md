# Rational Recovery from Finite Valuations

## Abstract

Finite prime valuations form a direct-sum profile that recovers nonzero rationals.

**Definition 1.1 (The finite-prime valuation profile).**

$$nu: \mathbb{Q} \to SignedPrimeLedger, nu(x)(p) = v_p(x).$$

*Formalization.* `D5/S3/Factorization/Embeddings/RationalValuationRecovery.rationalFiniteValuationProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The profile assigns to a rational number the integer p-adic valuation at each natural prime p. Its finite support is contained in the union of the numerator and denominator factorization supports, so the codomain is the signed-prime direct sum rather than an unrestricted product.

**Theorem 1.2 (Profile coordinates are p-adic valuations).**

$$\forall x \in \mathbb{Q}, p \in Nat.Primes, nu(x)(p) = v_p(x).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/RationalValuationRecovery.rationalFiniteValuationProfile_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating the finitely supported profile at a prime returns exactly the Mathlib p-adic valuation at that prime. The finite-support packaging therefore does not alter any coordinate.

**Theorem 1.3 (Profiles classify nonzero rationals up to sign).**

$$\forall x, y \in \mathbb{Q}, x \neq 0 \land y \neq 0 \Rightarrow (nu(x) = nu(y) \iff \left|x\right| = \left|y\right|).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/RationalValuationRecovery.rational_finite_valuation_profile_eq_iff_abs_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero rationals, equality of every finite-prime valuation is equivalent to equality of absolute values. The forward direction cross-multiplies the reduced numerator and denominator data and uses injectivity of natural-number prime factorization.

Primality is used for factorization coordinates and their uniqueness. No theorem about the distribution of primes is used, and merely assuming an index is greater than one would not identify a prime factorization coordinate.

**Theorem 1.4 (Sign and finite valuations recover a rational uniquely).**

$$\forall x, y \in \mathbb{Q}, x \neq 0 \land y \neq 0 \land nu(x) = nu(y) \land \operatorname{sgn}(x) = \operatorname{sgn}(y) \Rightarrow x = y.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/RationalValuationRecovery.rational_recovered_from_sign_and_finite_valuations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal profiles first identify absolute values. Equality of the nonzero archimedean signs then excludes the opposite-value branch, leaving equality of the original rationals.

**Theorem 1.5 (Finite valuations leave exactly a sign ambiguity).**

$$\forall x, y \in \mathbb{Q}, x \neq 0 \land y \neq 0 \land (\forall p, Prime(p) \Rightarrow v_p(x) = v_p(y)) \Rightarrow (x = y \lor x = -y).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/RationalValuationRecovery.rational_finite_valuation_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two nonzero rationals have equal p-adic valuations at every prime, then their absolute values agree. Consequently one rational equals either the other rational or its negative.

**Theorem 1.6 (Both nonzero hypotheses are necessary).**

$$(nu(0) = nu(1) \land 0 \neq 1 \land 0 \neq -1) \land (nu(1) = nu(0) \land 1 \neq 0 \land 1 \neq -0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/RationalValuationRecovery.nonzero_hypotheses_are_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The concrete pairs zero and one, in both orders, have identical finite valuations under Mathlib's totalized convention, but neither pair satisfies equality up to sign. Thus zero must be excluded on both sides.

**Theorem 1.7 (The sign observation is necessary).**

$$nu(1) = nu(-1) \land 1 \neq -1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/RationalValuationRecovery.sign_equality_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One and minus one have the same finite-prime profile but are unequal. This concrete kernel pair proves that valuation data alone cannot select a sign.

**Theorem 1.8 (The valuation observation is necessary).**

$$\operatorname{sgn}(1) = \operatorname{sgn}(2) \land 1 \neq 2.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/RationalValuationRecovery.valuation_equality_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive rationals one and two have equal signs but are unequal. This concrete pair proves that the sign readout cannot replace the finite valuation profile.

## References

- Truth anchor: `D5/S3/Factorization/Embeddings/RationalValuationRecovery.nonzero_hypotheses_are_necessary`
- Truth anchor: `D5/S3/Factorization/Embeddings/RationalValuationRecovery.rationalFiniteValuationProfile`
- Truth anchor: `D5/S3/Factorization/Embeddings/RationalValuationRecovery.rationalFiniteValuationProfile_apply`
- Truth anchor: `D5/S3/Factorization/Embeddings/RationalValuationRecovery.rational_finite_valuation_kernel`
- Truth anchor: `D5/S3/Factorization/Embeddings/RationalValuationRecovery.rational_finite_valuation_profile_eq_iff_abs_eq`
- Truth anchor: `D5/S3/Factorization/Embeddings/RationalValuationRecovery.rational_recovered_from_sign_and_finite_valuations`
- Truth anchor: `D5/S3/Factorization/Embeddings/RationalValuationRecovery.sign_equality_is_necessary`
- Truth anchor: `D5/S3/Factorization/Embeddings/RationalValuationRecovery.valuation_equality_is_necessary`
