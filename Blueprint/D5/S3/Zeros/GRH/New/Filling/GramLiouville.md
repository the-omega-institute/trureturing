# Gram Liouville

## Abstract

Gram Liouville

Discriminant of lattice points in a subspace; Liouville inequality for Gram determinants.

**Theorem 1.1 (sublatticeDisc_mul_index_sq_le).**

Lean statement: `D5/S3/Zeros/GRH/New/Filling/GramLiouville.sublatticeDisc_mul_index_sq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Filling/GramLiouville.sublatticeDisc_mul_index_sq_le` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let n have dim V columns, adelic combinations of vectors of V, with Hn integral, D = [det nᴴn] ≠ 0 and the columns of YHn in K. Let i be the index of K in the Ô-span of the columns of YHm, m = Filling.sublatticeBasis, d = Filling.sublatticeDisc. Then (d·i)² ≤ D, d > 0 and i ≥ 1.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Filling/GramLiouville.sublatticeDisc_mul_index_sq_le`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Algebra/LatticeComplement](../../Lib/General/Algebra/LatticeComplement.md)
- Dependency: [D5/S3/Zeros/GRH/New/Filling/LatticeChart](LatticeChart.md)
