# Fibre Sum

## Abstract

Fibre Sum

Cancelling disjoint sets of characters from two semisimple representations with equal trace differences. Traces of powers determine eigenvalues and characteristic polynomials in characteristic zero. Functions obeying all trace identities are traces of semisimple representations. det(1 - cN) as product over eigenvalues. A vanishing finite sum descends along a map, weighted by fibre sizes.

**Theorem 1.1 (exists_trace_limit).**

Lean statement: `D5/S3/Zeros/GRH/Lib/GaloisRep/Pseudocharacter/FibreSum.exists_trace_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/GaloisRep/Pseudocharacter/FibreSum.exists_trace_limit` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Given IsApproximatingMonoid s c N and continuous r_x, suppose for each g a proper filter on N has first coordinate eventually in a complete L, second tending to (tr r_x(g))_x. Then (tr R(g), (tr r_x(g))_x) ∈ N for all g, some continuous semisimple R.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/GaloisRep/Pseudocharacter/FibreSum.exists_trace_limit`
- Dependency: [D5/S3/Zeros/GRH/Lib/GaloisRep/Pseudocharacter/SemisimpleReps](SemisimpleReps.md)
