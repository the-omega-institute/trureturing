# Oscillator Pair

## Abstract

Oscillator Pair

Derivative of oscillator representation on polynomial vectors is the quadratic creation-annihilation operator. Real unitary dual pair on Fock space: unitarity, derivative, positivity on harmonics.

**Theorem 1.1 (oscillatorPair_detTwist).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Weil/Fock/OscillatorPair.oscillatorPair_detTwist`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Weil/Fock/OscillatorPair.oscillatorPair_detTwist` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

On the Fock space of R×C matrices with signs ε_rε′_c, the representations h ↦ (det h)^γ ω(x ↦ hx) of U(ε) and g ↦ (det g)^γ′ ω(x ↦ xg⁻¹) of U(ε′) form a OscillatorPair with σ = 1 and constants γ, γ′ + |R| (FockDualPair.std).

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Weil/Fock/OscillatorPair.oscillatorPair_detTwist`
- Dependency: [D5/S3/Zeros/GRH/Lib/DiscreteSeries/Rigidity/AnalyticVectors](../../DiscreteSeries/Rigidity/AnalyticVectors.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/DualPair/Kronecker](../DualPair/Kronecker.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/Fock/FockHarmonicCoeff](FockHarmonicCoeff.md)
