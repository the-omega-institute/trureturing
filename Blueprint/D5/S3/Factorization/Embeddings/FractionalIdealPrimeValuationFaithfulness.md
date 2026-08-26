# Fractional-Ideal Prime-Valuation Faithfulness

## Abstract

All nonzero-prime valuation coordinates faithfully recover a nonzero fractional ideal.

**Theorem 1.1 (All prime-ideal valuations determine the fractional ideal).**

$$\forall R, K: Type,\\{}{\operatorname{CommRing}(R) \land \operatorname{Field}(K) \land \operatorname{Algebra}(R, K) \land \operatorname{IsFractionRing}(R, K) \land \operatorname{IsDedekindDomain}(R)} \Rightarrow\\{}\forall I, J\in \operatorname{NonzeroFractionalIdeals}(R, K),\\{}{\forall p\in \operatorname{HeightOneSpectrum}(R), \operatorname{count}(K, p, I) = \operatorname{count}(K, p, J)} \Rightarrow I = J.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/FractionalIdealPrimeValuationFaithfulness.prime_valuation_observers_faithful` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R be a Dedekind domain and K a fraction field of R. The two objects are nonzero fractional ideals, exactly the carrier on which the prime-ideal exponents form group coordinates.

Each element of the height-one spectrum represents a nonzero prime ideal. The displayed premise compares the canonical integer count at every such prime.

The pinned library reconstruction theorem expresses each nonzero fractional ideal as the finite product of those prime powers. Pointwise equality of all exponents therefore identifies the two ideals.

## References

- Truth anchor: `D5/S3/Factorization/Embeddings/FractionalIdealPrimeValuationFaithfulness.prime_valuation_observers_faithful`
