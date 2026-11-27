# Hecke Value Height

## Abstract

Hecke Value Height

Inverse ratio of twisted Hecke values has height repaying one direction; product version.

**Theorem 1.1 (heightLe_inv_heckeValueProd_div).**

Lean statement: `D5/S3/Zeros/GRH/New/Rows/HeckeValueHeight.heightLe_inv_heckeValueProd_div`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Rows/HeckeValueHeight.heightLe_inv_heckeValueProd_div` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For m-fold twists θ(ι) satisfying Data.IsFitFamily and 1 ≤ j ≤ m, the numbers (Γ(θ(ι)^j)/Γ(1))⁻¹, Γ = Data.heckeValueProd, have height (HeightLe) at most 10m·x^999 + k(6B₀ − 𝖴), 𝖴 = Data.dirCost.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Rows/HeckeValueHeight.heightLe_inv_heckeValueProd_div`
- Dependency: [D5/S3/Zeros/GRH/New/Rows/MemberOrthogonality](MemberOrthogonality.md)
- Dependency: [D5/S3/Zeros/GRH/New/Rows/Separation](Separation.md)
