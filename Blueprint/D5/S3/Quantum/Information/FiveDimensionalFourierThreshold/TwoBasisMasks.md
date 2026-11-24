# From synthesis Gram bounds to measurement mass gaps

## Abstract

The small-mask upper Gram bound bounds the mass of complementary large masks from below. The balanced lower Gram bound makes the square synthesis map invertible and gives the balanced mass gap through its adjoint.

**Definition 1.1 (The two Born probability tables).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/TwoBasisMasks.basisLaw`

*Formalization.* `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/TwoBasisMasks.basisLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each row is the squared modulus of the inner product with a vector in one of the two orthonormal bases.

**Definition 1.2 (Synthesis on a selected set of basis columns).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/TwoBasisMasks.maskSynthesis`

*Formalization.* `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/TwoBasisMasks.maskSynthesis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The synthesis map sends the coordinate of each retained row to its basis vector. Its adjoint reads the corresponding amplitude.

**Theorem 1.3 (Mass gaps from two Gram bounds).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/TwoBasisMasks.spectralMaskGaps_of_synthesis`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/TwoBasisMasks.spectralMaskGaps_of_synthesis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The small-mask upper Gram bound bounds the mass of complementary large masks from below. The balanced lower Gram bound makes the square synthesis map invertible and gives the balanced mass gap through its adjoint.

## References

- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/TwoBasisMasks.basisLaw`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/TwoBasisMasks.maskSynthesis`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/TwoBasisMasks.spectralMaskGaps_of_synthesis`
- Dependency: [D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/HarmonicThreshold](HarmonicThreshold.md)
