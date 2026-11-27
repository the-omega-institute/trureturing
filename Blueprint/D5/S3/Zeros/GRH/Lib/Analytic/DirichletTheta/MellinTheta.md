# Mellin Theta

## Abstract

Mellin Theta

Gaussian theta series of a character: Poisson symmetry, Mellin transform is Gamma times L.

**Theorem 1.1 (thetaTailIntegral_zero_le_two_mul).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Analytic/DirichletTheta/MellinTheta.thetaTailIntegral_zero_le_two_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Analytic/DirichletTheta/MellinTheta.thetaTailIntegral_zero_le_two_mul` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For j ≤ 1, primitive non-principal χ mod q with χ(−1) = (−1)^j, T > 0 and q ≤ T²: ∫_0^∞ |θ(t)| dt/√t ≤ 2 ∫_{1/T}^∞ |θ(t)| dt/√t, where θ = gaussianTheta j χ.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Analytic/DirichletTheta/MellinTheta.thetaTailIntegral_zero_le_two_mul`
- Dependency: [D5/S3/Zeros/GRH/Lib/Analytic/PolyaVinogradov/PolyaVinogradov](../PolyaVinogradov/PolyaVinogradov.md)
