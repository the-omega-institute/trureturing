# Flensted Jensen Invariance

## Abstract

Flensted Jensen Invariance

Flensted-Jensen integral is analytic and independent of the accretive splitting.

**Theorem 1.1 (dsCoeff_eq_flenstedJensen).**

Lean statement: `D5/S3/Zeros/GRH/Lib/DiscreteSeries/FlenstedJensen/FlenstedJensenInvariance.dsCoeff_eq_flenstedJensen`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/DiscreteSeries/FlenstedJensen/FlenstedJensenInvariance.dsCoeff_eq_flenstedJensen` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Independence of the splitting: for a parameter l = 2λ of some gap, g in U(diag ε) and a block diagonal matrix a such that a⁻¹g has positive definite hermitian part, ψ_λ(g) is the normalised integral HCParam.flenstedJensen at (a, a⁻¹g).

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/DiscreteSeries/FlenstedJensen/FlenstedJensenInvariance.dsCoeff_eq_flenstedJensen`
- Dependency: [D5/S3/Zeros/GRH/Lib/DiscreteSeries/Holomorphic/MinorEquivariance](../Holomorphic/MinorEquivariance.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/DiscreteSeries/Rigidity/CasimirBound](../Rigidity/CasimirBound.md)
