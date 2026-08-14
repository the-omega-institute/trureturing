# Faithfulness of Signed Prime Logarithmic Length

## Abstract

Canonical rational logarithmic length faithfully embeds signed prime ledgers.

**Theorem 1.1 (Rational logarithmic length is injective).**

$$\operatorname{Injective}(rationalLogLength)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/SignedPrimeLogEmbedding.rational_log_length_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical logarithmic length distinguishes any two finite signed prime exponent ledgers. Thus the real-valued interface retains the complete ledger rather than only an additive summary.

Both positive-rational representatives are strictly positive, so injectivity of the real logarithm identifies their real values. Injectivity of the rational and unit coercions then identifies the positive rationals, and the existing prime-exponent equivalence recovers the original ledgers.

This repository-derived consequence uses the canonical positive-rational interface directly. It is adjacent to integer linear independence of prime logarithms but does not restate or reprove that separate theorem.

## References

- Truth anchor: `D5/S3/Factorization/Embeddings/SignedPrimeLogEmbedding.rational_log_length_injective`
- Dependency: [D5/S3/Factorization/PositiveRationalGroup](../PositiveRationalGroup.md)
