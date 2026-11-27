# Bessel Existence

## Abstract

Bessel Existence

Record tying a Bessel system to its weight, degree and discrete series projector. Point of controlled size, from Lagrange weights, where the Bessel phases cancel. A discrete series Bessel function explicitly large at a point where phases cancel.

**Theorem 1.1 (exists_isBesselFunction).**

Lean statement: `D5/S3/Zeros/GRH/New/DiscreteSeries/BesselExistence.exists_isBesselFunction`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/DiscreteSeries/BesselExistence.exists_isBesselFunction` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For continuous rep with ⟨v, rep(·)v⟩ = ψ_u, l HCParam.HasLargeGap, b ≥ 16, phase σ − σ̄ at x, ν right Haar on Shape.besselGraph, ν(‖p⁻¹x⁻¹sxp − 1‖ ≤ 1) ≤ bⁿ|∫θ dν|: some Bessel W = W∗(deg·ψ) has W(x) ≠ 0, ‖W(y)‖ ≤ ∫|ψ(x⁻¹sy)|dν, ∫(2/‖p⁻¹x⁻¹syp‖)^N dν ≤ b^{N+n}‖W(x)‖ for all y, N = 8·rank²+1; θ = HCParam.laplaceIntegrand, σ = simpleRootSum.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/DiscreteSeries/BesselExistence.exists_isBesselFunction`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Algebra/ZerosCostDegree](../../Lib/General/Algebra/ZerosCostDegree.md)
- Dependency: [D5/S3/Zeros/GRH/New/DiscreteSeries/TwoFactorSetup](TwoFactorSetup.md)
- Dependency: [D5/S3/Zeros/GRH/New/RealPlace/BesselOrthonormal](../RealPlace/BesselOrthonormal.md)
