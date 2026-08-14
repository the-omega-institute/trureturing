# Density of Signed Prime Logarithmic Length

## Abstract

Canonical rational logarithmic length is dense in the real line.

**Theorem 1.1 (Rational logarithmic length has dense range).**

$$\operatorname{DenseRange}(rationalLogLength)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/SignedPrimeLogDensity.rational_log_length_dense` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical logarithmic lengths of finite signed prime exponent ledgers form a dense subset of the real line. Equivalently, every nonempty real open interval contains the logarithmic length of a signed prime ledger.

Exponentiation sends the endpoints of any such interval to two strictly ordered positive reals. A rational between those values is positive, hence defines a unit of the nonnegative rationals and therefore a signed prime ledger through the existing equivalence. The logarithm and exponential order equivalences return its length to the original interval.

This repository-derived consequence reuses the canonical positive-rational interface. Pinned Mathlib supplies rational density through exists_rat_btwn, interval density through dense_of_exists_between, and the strict logarithm-exponential order equivalences used for both endpoint bounds.

## References

- Truth anchor: `D5/S3/Factorization/Embeddings/SignedPrimeLogDensity.rational_log_length_dense`
- Dependency: [D5/S3/Factorization/PositiveRationalGroup](../PositiveRationalGroup.md)
