# Admissible Data

## Abstract

Admissible Data

Record of admissible data; names for ranks, weights, the prime sum, the error budget and the cost of one direction.

**Definition 1.1 (dirCost).**

Lean statement: `D5/S3/Zeros/GRH/New/Data/AdmissibleData.dirCost`

*Formalization.* `D5/S3/Zeros/GRH/New/Data/AdmissibleData.dirCost` (`✓ std3`).

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

The cost of one direction: the sum over infinite places σ of jetSize(w₀(σ)) − primeSum(w(σ), σ), with Data.jetSize, Data.primeSum and the nominal weight w = Data.nominalWeight.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Data/AdmissibleData.dirCost`
- Dependency: [D5/S3/Zeros/GRH/New/Curve/ConjugateGenerator](../Curve/ConjugateGenerator.md)
