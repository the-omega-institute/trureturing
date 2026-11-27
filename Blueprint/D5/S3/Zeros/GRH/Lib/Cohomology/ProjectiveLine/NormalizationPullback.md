# Normalization Pullback

## Abstract

Normalization Pullback

Projective line formula for tilted O/p coefficients via a left inverse of cup with η. Projective line formula for mod-l cohomology over bases mapping to fields or C_p. Loci keeping coincidences among finitely many maps to a proper functor form a cover. Comparison property for opens of affine space in (P¹)^d and standard étale charts. Pull-back along a finite linear projection to projective space is injective (transfer).

**Theorem 1.1 (pullback_injective).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Cohomology/ProjectiveLine/NormalizationPullback.pullback_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Cohomology/ProjectiveLine/NormalizationPullback.pullback_injective` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let L embed Y, g be coordinates of a field point, Λ a Noether normalisation of g. If O ⊂ Γ ⊂ Y × P^d contains (x,[Λ(v)]) whenever coordinates v of x satisfy the homogeneous equations of g, pull-back along O → P^d is injective on H^n on p-adic tests with coefficient genericCoeff.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Cohomology/ProjectiveLine/NormalizationPullback.pullback_injective`
- Dependency: [D5/S3/Zeros/GRH/Lib/Cohomology/Kunneth/LerayHirschBasis](../Kunneth/LerayHirschBasis.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Cohomology/PointClass/HomogeneousCoords](../PointClass/HomogeneousCoords.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Cohomology/PointClass/LocusEquations](../PointClass/LocusEquations.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Cohomology/ProjectiveLine/PerfectLine](PerfectLine.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicComparison/Duality/IntegrationOverLine](../../PadicComparison/Duality/IntegrationOverLine.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicComparison/Primitive/TiltedTheory](../../PadicComparison/Primitive/TiltedTheory.md)
