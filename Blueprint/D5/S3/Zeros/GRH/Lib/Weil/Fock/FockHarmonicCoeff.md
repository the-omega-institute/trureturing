# Fock Harmonic Coeff

## Abstract

Fock Harmonic Coeff

Functional bounded by its small-shift differences decays as any power of the shift. Fock inner product equals Fischer product; polynomials dense; intertwining relations for coefficients. Matrix coefficients of the oscillator representation between harmonic polynomials.

**Theorem 1.1 (fockMatrixCoeff_eq_realInner).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Weil/Fock/FockHarmonicCoeff.fockMatrixCoeff_eq_realInner`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Weil/Fock/FockHarmonicCoeff.fockMatrixCoeff_eq_realInner` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let u in U(ε) be block diagonal for labels d, and ∂_i∂_j kill P, Q whenever d_i = d_j, ε_i ≠ ε_j. Then ⟨v_Q, ω₀(u)v_P⟩ = (det u₋)⁻¹⟨v_Q′, v_P⟩, u₋ the negative block, Q′ = Q under X_j ↦ ∑_i A_ij X_i, A = (complexLinearPart u)⁻¹.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Weil/Fock/FockHarmonicCoeff.fockMatrixCoeff_eq_realInner`
- Dependency: [D5/S3/Zeros/GRH/Lib/DiscreteSeries/CuspKernel/CircleMean](../../DiscreteSeries/CuspKernel/CircleMean.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/DiscreteSeries/Theta/OscillatorDefs](../../DiscreteSeries/Theta/OscillatorDefs.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/GLn/SchurModule/Nabla](../../GLn/SchurModule/Nabla.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/Fock/MixedFockModel](MixedFockModel.md)
