# Parahoric Type Label

## Abstract

Parahoric Type Label

Parahoric types and depth-zero labels; type implies label by Frobenius reciprocity.

**Theorem 1.1 (hasProductLabel).**

Lean statement: `D5/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/ParahoricTypeLabel.hasProductLabel`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/ParahoricTypeLabel.hasProductLabel` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Type implies label (Frobenius reciprocity): let c be a label of degree |ρ|, c' its roots scaled by x_ψ, the χ_l distinct, c'(x_{χ_l}) ≠ 0, and Σ conj(Ξ_c(x))F(x) ≠ 0. Then HasParahoricType gives HasProductLabel for c', the χ_l and the block sizes.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/ParahoricTypeLabel.hasProductLabel`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/BlockMatrices](../../General/LinearAlgebra/BlockMatrices.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/LocalGL/Shintani/ShintaniLifting](../../LocalGL/Shintani/ShintaniLifting.md)
