# Ordinary Petz recovery on a radial qubit segment

## Abstract

Ordinary Petz recovery after binary projective measurement satisfies the coefficient-two bound on the closed radial qubit segment.

**Theorem 1.1 (Coefficient two and the reference logarithm).**

Lean statement: `D5/S3/Quantum/Recovery/PetzBinaryProjectiveRadialBound.radial_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzBinaryProjectiveRadialBound.radial_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take real u, z, R and a with R² = u² + z², 0 ≤ z ≤ R < 1 and 0 ≤ a ≤ 1. The input is the qubit with Bloch coordinates (au, 0, az) and the reference has coordinates (u, 0, z). Measure in the computational basis and recover by the ordinary Petz action built from the positive square root of the reference.

Write Δ for the finite trace-log relative entropy before measurement minus its value after measurement. Let E be the squared full trace norm of the difference between the input and the recovered state. Put L = log((1 − z²)/(1 − R²)) and ξ = (R² − z²)/(1 − z²). Then E ≤ 2Δ, (1 − a)² L/2 ≤ Δ, and LE ≤ 2ξΔ. These inequalities include a = 0, a = 1 and ξ = 0.

The input and reference share a spectral basis, where scaling a reference eigenvalue λ gives aλ + (1 − a)/2. The two measured states already share the computational basis. The difference of the two negative binary entropies has nondecreasing second derivative along the segment. This controls the relative entropy loss by its value at the maximally mixed input. Expanding the Petz sandwich and using the trace norm of a traceless symmetric qubit matrix gives E = (1 − a)²ξ.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PetzBinaryProjectiveRadialBound.radial_bounds`
- Dependency: [D5/S3/Quantum/CommutingMidpoint/Fidelity](../CommutingMidpoint/Fidelity.md)
- Dependency: [D5/S3/Quantum/Information/QubitNormalFormState](../Information/QubitNormalFormState.md)
- Dependency: [D5/S3/Quantum/Recovery/PetzBinaryProjectiveOverFive](PetzBinaryProjectiveOverFive.md)
- Dependency: [D5/S3/QuantumChannels/ContractionSpectrumOrder](../../QuantumChannels/ContractionSpectrumOrder.md)
