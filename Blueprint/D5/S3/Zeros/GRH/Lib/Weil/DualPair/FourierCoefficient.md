# Fourier Coefficient

## Abstract

Fourier Coefficient

Real mixed model of an adapted splitting; slices factor into real and finite parts. Mixed-model terms of a theta kernel: equivariance, moderate growth, integrability for onto data. Fourier coefficient of a theta lift as sum over frames, unfolded by Witt.

**Theorem 1.1 (centreCoeff_eq_integral_stabilizer).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Weil/DualPair/FourierCoefficient.centreCoeff_eq_integral_stabilizer`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Weil/DualPair/FourierCoefficient.centreCoeff_eq_integral_stabilizer` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Unfolding: let y be continuous, left Γ-invariant, satisfying Space.Splitting.HasIntegrableTerms, x₀ rational with invertible Gram matrix β, S the rational stabiliser of x₀. The x₀-term times y is S-invariant, integrable modulo S, with integral the Fourier coefficient at ȷβ and g of y's lift.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Weil/DualPair/FourierCoefficient.centreCoeff_eq_integral_stabilizer`
- Dependency: [D5/S3/Zeros/GRH/Lib/SiegelWeil/SingularForms/AdaptedHom](../../SiegelWeil/SingularForms/AdaptedHom.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/DualPair/KernelDecay](KernelDecay.md)
