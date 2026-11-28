# Poincare Series

## Abstract

Poincare Series

Poincaré series from cut-off Bessel function: convergence, being a form, unfolding, inner products.

**Theorem 1.1 (petersson_poincare).**

Lean statement: `D5/S3/Zeros/GRH/New/Filling/PoincareSeries.petersson_poincare`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Filling/PoincareSeries.petersson_poincare` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Unfolding. Under Filling.IsAdmissible, for coordinate columns a = (c, i), a' = (c', i') and k in K₀ with reduction s, the Petersson product ⟨k𝒫a', 𝒫a⟩ is the volume of Filling.stdPrincipalLevel times entry (i, i') of the amplitude sum over all rational terms over (c, s, c').

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Filling/PoincareSeries.petersson_poincare`
- Dependency: [D5/S3/Zeros/GRH/New/DiscreteSeries/BesselExistence](../DiscreteSeries/BesselExistence.md)
- Dependency: [D5/S3/Zeros/GRH/New/Filling/AmplitudeSums](AmplitudeSums.md)
- Dependency: [D5/S3/Zeros/GRH/New/Seesaw/GradingsOfY](../Seesaw/GradingsOfY.md)
