# Coordinate and Fourier Born laws

## Abstract

Splitting the sum over the two bases gives the computational readout and the inverse-QFT readout.

**Definition 1.1 (The normalized Fourier orthonormal basis).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveBasis.fourierBasis`

*Formalization.* `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveBasis.fourierBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The basis columns use the repository QFT. Their coordinate map is the inverse QFT, which preserves the Euclidean norm.

**Theorem 1.2 (The normalized Fourier kernel entry).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveBasis.fourierBasis_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveBasis.fourierBasis_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the QFT to a coordinate unit vector selects a single normalized kernel value.

**Theorem 1.3 (The two five-row score sums).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveBasis.fiveScore_eq_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveBasis.fiveScore_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Splitting the sum over the two bases gives the computational readout and the inverse-QFT readout.

## References

- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveBasis.fiveScore_eq_sum`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveBasis.fourierBasis`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveBasis.fourierBasis_entry`
- Dependency: [D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/TwoBasisMasks](TwoBasisMasks.md)
- Dependency: [D5/S3/Quantum/ShorCountingMarginal](../../ShorCountingMarginal.md)
