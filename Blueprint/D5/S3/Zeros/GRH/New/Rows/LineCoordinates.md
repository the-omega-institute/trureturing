# Line Coordinates

## Abstract

Line Coordinates

Names for index sets, characters, moduli and polynomials of the comparison construction. Column counts of the weight add up to w_j − j − ⌊(t+k−1)/2⌋. Index sets, determinant data and coefficient vectors for the one-line identity. Degree, denominator and size of coordinates of the determinant product in Weyl's lattice.

**Theorem 1.1 (exists_denom_linePolyCoords).**

Lean statement: `D5/S3/Zeros/GRH/New/Rows/LineCoordinates.exists_denom_linePolyCoords`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Rows/LineCoordinates.exists_denom_linePolyCoords` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For 1 ≤ j ≤ m there are d ≤ 31m·∑_τ |Data.DetIndex j τ| and an integer 0 < H ≤ d^{3d} such that every H·Data.linePolyCoords is homogeneous of degree d, with coefficients in any subring of ℂ containing all τ(Y_ab).

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Rows/LineCoordinates.exists_denom_linePolyCoords`
- Dependency: [D5/S3/Zeros/GRH/Lib/Adelic/Hecke/ClassSumBounds](../../Lib/Adelic/Hecke/ClassSumBounds.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/LocalGL/TraceFormula/TraceComparison](../../Lib/LocalGL/TraceFormula/TraceComparison.md)
- Dependency: [D5/S3/Zeros/GRH/New/Rows/MemberKernels](MemberKernels.md)
- Dependency: [D5/S3/Zeros/GRH/New/Trace/GoodIdempotent](../Trace/GoodIdempotent.md)
