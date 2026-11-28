# Marked Prime Type

## Abstract

Marked Prime Type

Scaled Hecke operator at a marked prime has image of small index on columns.

**Theorem 1.1 (hasType_markOperator).**

Lean statement: `D5/S3/Zeros/GRH/New/Columns/MarkedPrimeType.hasType_markOperator`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Columns/MarkedPrimeType.hasType_markOperator` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For Λ marked at p, l in Λ and any s, the operator p^{A_l}T_{l,𝔯} (Data.IsMarked.markOperator) keeps the integral columns and is onto modulo p^s up to an index of exponent at most (128A_l log b/(mp) + s/x^14 + x^40)·dim(columns) (HasType).

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Columns/MarkedPrimeType.hasType_markOperator`
- Dependency: [D5/S3/Zeros/GRH/New/Columns/TwistedHeckeType](TwistedHeckeType.md)
