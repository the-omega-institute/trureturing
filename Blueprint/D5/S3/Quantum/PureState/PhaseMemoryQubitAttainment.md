# Qubit strategies attaining the clipped score

## Abstract

Explicit common qubit encoders for Walsh and symmetric Fourier phases.

Put r = √(t₁² + t₂² + t₃²) > 0. Each construction sends the four input coordinates to an orthonormal operator basis, viewed as two-qubit vectors and divided by √2. Tracing out the second qubit gives the same CPTP encoder for every input. The coefficient matrix before the partial trace has the form (t₀I + Bⱼ)/√2 with Bⱼ Hermitian and traceless, Bⱼ² = r²I and ΣⱼBⱼ = 0. The positive-eigenvalue projector Rⱼ = (I + Bⱼ/r)/2 has trace one. The four effects Rⱼ/2 sum to I and yield score (t₀ + r)²/4.

**Theorem 1.1 (The Pauli basis gives an attaining Walsh encoder).**

Lean statement: `D5/S3/Quantum/PureState/PhaseMemoryQubitAttainment.walsh4_attains`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseMemoryQubitAttainment.walsh4_attains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the coefficient matrices I, X, Y and Z in Walsh order. The Walsh signs make the last three coefficients real, and the Pauli anticommutation relations give Bⱼ² = r²I.

**Theorem 1.2 (Equal conjugate-frequency amplitudes give an attaining Fourier encoder).**

Lean statement: `D5/S3/Quantum/PureState/PhaseMemoryQubitAttainment.symmetric_fourier4_attains`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseMemoryQubitAttainment.symmetric_fourier4_attains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use I, √2 E₀₁, Z and √2 E₁₀. At t₁ = t₃ the off-diagonal entries have conjugate Fourier phases with equal magnitude, so the tail is Hermitian. Its square is r²I, which gives the same decoder construction.

## References

- Truth anchor: `D5/S3/Quantum/PureState/PhaseMemoryQubitAttainment.symmetric_fourier4_attains`
- Truth anchor: `D5/S3/Quantum/PureState/PhaseMemoryQubitAttainment.walsh4_attains`
- Dependency: [D5/S3/Quantum/PureState/PhaseMemoryCompact](PhaseMemoryCompact.md)
- Dependency: [D5/S3/Quantum/PureState/PhaseMemorySaturatedFrame](PhaseMemorySaturatedFrame.md)
