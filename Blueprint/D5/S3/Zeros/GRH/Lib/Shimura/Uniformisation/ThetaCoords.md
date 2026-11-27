# Theta Coords

## Abstract

Theta Coords

Rigid objects: theta coordinates span sections; theta law over local rings. Multiplication by nonzero a is an isogeny; counting torsion points over C. Line bundles with theta coordinates: pull-back, product, translation, uniqueness in Appell-Humbert.

**Theorem 1.1 (riemannForm_eq_of_isFrame).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/ThetaCoords.riemannForm_eq_of_isFrame`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/ThetaCoords.riemannForm_eq_of_isFrame` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let N, M have theta coordinates θ, θ' of types (B, χ), (B', χ') for a full lattice L along a holomorphic L-periodic e, and w trivialise N ⊗ M⁻¹. Then Riemann forms agree, χ = χ' on L, and w_{ia}(e z) = c·exp((B(z,z) − B'(z,z))/2)·θ'_a(z)/θ_i(z) where both are non-zero, c constant.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/ThetaCoords.riemannForm_eq_of_isFrame`
- Dependency: [D5/S3/Zeros/GRH/Lib/Shimura/AbelianScheme/ThetaFamily](../AbelianScheme/ThetaFamily.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Shimura/GoodReduction/ThetaOrthogonality](../GoodReduction/ThetaOrthogonality.md)
