# Pauli frame overlap bounds

## Abstract

Anticommuting Hermitian involutions give real orthonormal frames and two bounds on sums of complex squared overlaps.

Rotating the identity slot by i gives real orthogonality. Applying the real Bessel inequality to u and iu bounds the complex squared overlaps. The ordered product of all four signed Pauli words transfers this bound to the complementary products.

**Theorem 1.1 (Real orthonormality).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointPauliFrame.real_orthonormal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuEndpointPauliFrame.real_orthonormal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a unit vector, the images under symmetric anticommuting involutions and the vector rotated by i form a real orthonormal family.

**Theorem 1.2 (Identity and single Pauli words).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointPauliFrame.pauli_frame_overlap_le_two`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuEndpointPauliFrame.pauli_frame_overlap_le_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum of the squared overlaps of u with v and with the four single-word images of v is at most 2‖u‖²‖v‖².

**Theorem 1.3 (Triple and full Pauli products).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointPauliFrame.pauli_tail_overlap_le_two`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuEndpointPauliFrame.pauli_tail_overlap_le_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum of the squared overlaps of u with the four triple-word images and the full-product image of v is at most 2‖u‖²‖v‖².

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointPauliFrame.pauli_frame_overlap_le_two`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointPauliFrame.pauli_tail_overlap_le_two`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointPauliFrame.real_orthonormal`
- Dependency: [D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation](../Measurement/StabilizerPovmMaximalEntanglementRefutation.md)
- Dependency: [D5/S3/Quantum/Semigroups/WuRankOneEndpointClifford](WuRankOneEndpointClifford.md)
