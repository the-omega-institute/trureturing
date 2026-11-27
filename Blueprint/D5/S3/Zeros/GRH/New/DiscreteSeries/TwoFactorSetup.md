# Two Factor Setup

## Abstract

Two Factor Setup

Steep parameters, phase cancellation; integrand is large only near diagonal U(X).

**Theorem 1.1 (exists_near_one).**

Lean statement: `D5/S3/Zeros/GRH/New/DiscreteSeries/TwoFactorSetup.exists_near_one`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/DiscreteSeries/TwoFactorSetup.exists_near_one` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Assume IsTwoFactor, B ≥ 1, 0 < r ≤ 1/100. If j(s) = (g, g') has ‖g−a_g‖²+‖g'−a_{g'}‖² ≤ r² (Frobenius, a the block diagonal part), some t has θ(t) = θ(s), θ = HCParam.laplaceIntegrand, with both components of j(t)−1 of norm ≤ 10r.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/DiscreteSeries/TwoFactorSetup.exists_near_one`
- Dependency: [D5/S3/Zeros/GRH/New/DiscreteSeries/GaussianShape](GaussianShape.md)
