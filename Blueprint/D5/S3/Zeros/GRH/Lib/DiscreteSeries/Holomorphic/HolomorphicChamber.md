# Holomorphic Chamber

## Abstract

Holomorphic Chamber

Discrete series coefficient equals a product of minors in the holomorphic chamber.

**Theorem 1.1 (dsCoeff_eq_holMinors).**

Lean statement: `D5/S3/Zeros/GRH/Lib/DiscreteSeries/Holomorphic/HolomorphicChamber.dsCoeff_eq_holMinors`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/DiscreteSeries/Holomorphic/HolomorphicChamber.dsCoeff_eq_holMinors` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Holomorphic discrete series: order o with signs +1 first, w K-dominant, w_i+γ ≤ w_j for ε_i = 1, ε_j = −1, γ > 500n³+A+n+1, λ_i = w_i + (n+1)/2 − i with i the rank in o. Then λ has gap 500n³+A and ψ_λ = holMinors ε w on U(diag ε).

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/DiscreteSeries/Holomorphic/HolomorphicChamber.dsCoeff_eq_holMinors`
- Dependency: [D5/S3/Zeros/GRH/Lib/DiscreteSeries/Holomorphic/HolomorphicMinor](HolomorphicMinor.md)
