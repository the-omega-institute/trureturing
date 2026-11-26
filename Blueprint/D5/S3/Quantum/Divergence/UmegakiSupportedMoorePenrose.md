# Supported Moore–Penrose arithmetic inverse

## Abstract

Bounded arithmetic inverse tests are exactly the range-supported Moore–Penrose form.

**Theorem 1.1 (Range and maximizing preimage).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiSupportedMoorePenrose.variationalInverse_moorePenrose`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiSupportedMoorePenrose.variationalInverse_moorePenrose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite positive semidefinite base Z and t in [0,1], the test values are bounded above exactly when the Hilbert–Schmidt direction belongs to the range of Aₜ = (1−t)L_Z + tR_Z. A real scaling of any complex kernel direction tests orthogonality to the kernel. Self-adjointness then gives range membership.

On this range, complete the square about the preimage from FiniteMoorePenroseInverse. The test reaches its supremum there, and the value is the real Hilbert–Schmidt pairing of the direction with its Moore–Penrose inverse image.

**Theorem 1.2 (Range at the actual channel output).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiSupportedMoorePenrose.variationalInverse_output_moorePenrose`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiSupportedMoorePenrose.variationalInverse_output_moorePenrose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For t in [0,1], a positive semidefinite input base and a complex direction of zero partial trace, bounded input test values put the amplified direction in the range of the arithmetic map of the actual amplified base. The output value is its supported Moore–Penrose pairing.

**Theorem 1.3 (Metric ratios in Moore–Penrose coordinates).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiSupportedMoorePenrose.variationalMetricCoefficient_eq_sSup_moorePenrose`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiSupportedMoorePenrose.variationalMetricCoefficient_eq_sSup_moorePenrose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each t in [0,1] the metric coefficient is the supremum of the same ratios with the supported Moore–Penrose numerator and faithful inverse denominator. Every admissible input in the metric ratio set supplies the required output-range membership.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiSupportedMoorePenrose.variationalInverse_moorePenrose`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiSupportedMoorePenrose.variationalInverse_output_moorePenrose`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiSupportedMoorePenrose.variationalMetricCoefficient_eq_sSup_moorePenrose`
- Dependency: [D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse](../../Observer/Hilbert/FiniteMoorePenroseInverse.md)
- Dependency: [D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension](UmegakiChannelSupportedExtension.md)
