# Orthogonal Sum

## Abstract

Orthogonal Sum

Tensor products of Heisenberg vacuum models; Wiener amalgam bound for coefficients.

**Theorem 1.1 (wiener_bound).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Weil/Construction/OrthogonalSum.wiener_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Weil/Construction/OrthogonalSum.wiener_bound` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Wiener-type bound: T bounded, κ: W₁ → W a continuous homomorphism, u(0) ≠ 0, ‖Tρ(z+κx)u‖ = ‖g(t(z)+x)‖, g integrable. Some compact B ⊆ W₁ and M give ∑_i ‖Tρ(κφ(i))v‖ ≤ #φ⁻¹(B)·M·‖v‖ for all homomorphisms φ: I → W₁ and all v.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Weil/Construction/OrthogonalSum.wiener_bound`
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/Construction/WeilOperators](WeilOperators.md)
