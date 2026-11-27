# Parahoric Columns

## Abstract

Parahoric Columns

Local matching of pro-p Iwahori double cosets of t and its norm. Sums over columns of a parahoric, counting vectors by last non-zero coordinate.

**Theorem 1.1 (exists_line_orbit_sums).**

Lean statement: `D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/ParahoricColumns.exists_line_orbit_sums`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/ParahoricColumns.exists_line_orbit_sums` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let P ⊂ GL_N(𝒪) have columns before m in 𝔭 below the diagonal, x be fixed by the p ∈ P with column m in 𝔭 off the diagonal, φ Iwahori-invariant, a_j = (q−1)q^j φ((m j)x), indices from 0. Some P-fixed y has φ(y) = ∑_{j≥m} a_j; some z, fixed by the p ∈ P with row m in 𝔭 off the diagonal, has φ((m i)z) = a_i + (1−1/q)∑_{j>i} a_j for i ≥ m.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/ParahoricColumns.exists_line_orbit_sums`
- Dependency: [D5/S3/Zeros/GRH/Lib/LocalGL/Iwahori/HeckeCounts](../../LocalGL/Iwahori/HeckeCounts.md)
