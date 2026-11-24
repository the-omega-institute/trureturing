# Bounds on rectangular five-point Fourier compressions

## Abstract

Transpose symmetry reduces the estimate to zero, one, or two columns when the total selected indices are at most five. The two-column Gram off-diagonal is a pentagon phase sum.

**Definition 1.1 (The rectangular Fourier form).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveCrossBound.crossForm`

*Formalization.* `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveCrossBound.crossForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The form pairs two supported coefficient vectors through the normalized Fourier entries of the corresponding rectangular submatrix.

**Theorem 1.2 (The exact compression bounds).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveCrossBound.crossForm_sq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveCrossBound.crossForm_sq_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transpose symmetry reduces the estimate to zero, one, or two columns when the total selected indices are at most five. The two-column Gram off-diagonal is a pentagon phase sum.

## References

- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveCrossBound.crossForm`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveCrossBound.crossForm_sq_le`
- Dependency: [D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFivePhases](FourierFivePhases.md)
