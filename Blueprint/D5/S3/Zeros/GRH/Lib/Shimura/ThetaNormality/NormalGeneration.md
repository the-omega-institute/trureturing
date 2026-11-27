# Normal Generation

## Abstract

Normal Generation

Every point is centre of a rank-one valuation at a dense complex point. Finite products of proper schemes over a base are proper. Sup-norm balls of theta functions: powers of balls are balls, rank of reduction.

**Theorem 1.1 (thetaNorm_lt_iff_coords).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Shimura/ThetaNormality/NormalGeneration.thetaNorm_lt_iff_coords`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Shimura/ThetaNormality/NormalGeneration.thetaNorm_lt_iff_coords` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Assume HasGoodReduction. Let (x_j) enumerate the ball of a theta function f ≠ 0, (a_b) meet every class of L^∨/L, and p_b primitively scale (x_j(a_b))_j. Then ‖x_j‖ < ‖f‖ iff p_{b,j} is a non-unit for all b.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Shimura/ThetaNormality/NormalGeneration.thetaNorm_lt_iff_coords`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Geometry/ReducedClosure](../../General/Geometry/ReducedClosure.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Shimura/GoodReduction/ThetaOrthogonality](../GoodReduction/ThetaOrthogonality.md)
