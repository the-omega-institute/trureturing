# Gaussian Shape

## Abstract

Gaussian Shape

Near 1 the coefficient is explicit phase times real factor, uniform error.

**Theorem 1.1 (dsCoeff_gaussian_shape).**

Lean statement: `D5/S3/Zeros/GRH/New/DiscreteSeries/GaussianShape.dsCoeff_gaussian_shape`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/DiscreteSeries/GaussianShape.dsCoeff_gaussian_shape` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Gaussian shape: let l = 2λ have gap 500n³, |l_a| ≤ L, T ≥ max(1, n², n² log(n+L+1)), 10¹²δT ≤ 1, ‖g−1‖ ≤ δ (Frobenius). Then |ψ_λ(g)/exp tr(diag(Λ) log g) − κ| ≤ κ/10 + e^{−100T} for some κ∈[0,1], log g = logOneAdd(g−1), Λ = HCParam.lowestKType.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/DiscreteSeries/GaussianShape.dsCoeff_gaussian_shape`
- Dependency: [D5/S3/Zeros/GRH/Lib/DiscreteSeries/FlenstedJensen/TailBounds](../../Lib/DiscreteSeries/FlenstedJensen/TailBounds.md)
- Dependency: [D5/S3/Zeros/GRH/New/DiscreteSeries/MinorExpansion](MinorExpansion.md)
