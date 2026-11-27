# Block Partners

## Abstract

Block Partners

Sections over cosets; matched pairs are GL-stable and determined by one side. Block determinant functions on the open cell are partners, by Jacobi's complementary minors.

**Theorem 1.1 (partner_block).**

Lean statement: `D5/S3/Zeros/GRH/New/Exchange/BlockPartners.partner_block`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Exchange/BlockPartners.partner_block` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For any function f, the functions Φ(x₁ x₂) = χ⁻¹(det x₂)f(x₂⁻¹x₁) and Ψ(y₁; y₂) = χ⁻¹(det y₁)f(−y₂y₁⁻¹), with blocks cut by e and x₂, y₁ square, are partners for χ over R (IsPartner).

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Exchange/BlockPartners.partner_block`
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/GaussSum/ShearInvariance](../../Lib/Weil/GaussSum/ShearInvariance.md)
