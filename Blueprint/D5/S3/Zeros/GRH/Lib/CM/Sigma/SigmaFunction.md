# Sigma Function

## Abstract

Sigma Function

From degree two on, theta functions have no common zero. Sigma function as odd canonical theta function; zeros, dimension, addition formula.

**Theorem 1.1 (sigma_add_mul_sigma_sub).**

Lean statement: `D5/S3/Zeros/GRH/Lib/CM/Sigma/SigmaFunction.sigma_add_mul_sigma_sub`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/CM/Sigma/SigmaFunction.sigma_add_mul_sigma_sub` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Addition formula for the sigma function of L: for u and v outside the lattice, σ(u + v)·σ(u − v) = (℘(v) − ℘(u))·σ(u)²·σ(v)².

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/CM/Sigma/SigmaFunction.sigma_add_mul_sigma_sub`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/HuaIntegral](../../General/LinearAlgebra/HuaIntegral.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Shimura/ComplexTheta/ThetaDimension](../../Shimura/ComplexTheta/ThetaDimension.md)
