# Smooth Base Change

## Abstract

Smooth Base Change

Duality comparison globalised; smooth schemes over valuation rings keep cohomology on the generic fibre.

**Theorem 1.1 (isCohomEquiv_generic_fibre).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Cohomology/SmoothBaseChange/SmoothBaseChange.isCohomEquiv_generic_fibre`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Cohomology/SmoothBaseChange/SmoothBaseChange.isCohomEquiv_generic_fibre` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let A be a valuation subring of Ω and an R-algebra, with a prime p in its maximal ideal and ℓ invertible. If the R-scheme Y satisfies IsCharted over R, then pull-back Hⁿ(Y_A, ℤ/ℓ) → Hⁿ(Y_Ω, ℤ/ℓ) is bijective for all n.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Cohomology/SmoothBaseChange/SmoothBaseChange.isCohomEquiv_generic_fibre`
- Dependency: [D5/S3/Zeros/GRH/Lib/ClassField/Places/DecompositionLocal](../../ClassField/Places/DecompositionLocal.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Cohomology/ProjectiveLine/NormalizationPullback](../ProjectiveLine/NormalizationPullback.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Geometry/ChartedSchemes](../../General/Geometry/ChartedSchemes.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicComparison/Primitive/PrimitivePeriods](../../PadicComparison/Primitive/PrimitivePeriods.md)
