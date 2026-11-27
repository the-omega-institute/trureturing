# Padic Decomposition

## Abstract

Padic Decomposition

Ax-Sen-Tate: fixed points in C_p are limits of fixed algebraic numbers. Decomposition group identified with Galois group of the p-adic completion (Krasner).

**Theorem 1.1 (exists_inducesPlace).**

Lean statement: `D5/S3/Zeros/GRH/Lib/ClassField/Places/PadicDecomposition.exists_inducesPlace`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/ClassField/Places/PadicDecomposition.exists_inducesPlace` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

An embedding ι : Ω → Q̄_p pulling the integers back to A induces an open embedding j of the decomposition group of A in Gal(Q̄_p/ℚ_p), with j(g)(ιx) = ι(gx), whose image consists of the automorphisms fixing ι(K) pointwise.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/ClassField/Places/PadicDecomposition.exists_inducesPlace`
- Dependency: [D5/S3/Zeros/GRH/Lib/ClassField/Places/UnramifiedCharacters](UnramifiedCharacters.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicHodge/PeriodRings/CpIntegers](../../PadicHodge/PeriodRings/CpIntegers.md)
