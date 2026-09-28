# Rectangular Variational Bound

## Abstract

Rectangular singular-value prefix bounds used by the passive sector test.

The Ky Fan sum is the sum of the first k singular values of a finite linear map between real or complex inner-product spaces. The domain and codomain dimensions may differ. These selected arguments adapt AIQ-Kitware/aiq-dkps-formalization revision 64e234954217f3ca907ac980c8cbde2900109a66 under Apache-2.0. The port retires when this repository's pinned Mathlib has equivalent results.

**Definition 1.1 (Ky Fan singular-value sum).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteSectorRectangularVariational.kyFanSum`

*Formalization.* `D5/S3/Quantum/Entanglement/FiniteSectorRectangularVariational.kyFanSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural prefix length k, sum the first k singular values, with zero extension beyond the source dimension.

**Theorem 1.2 (Orthonormal variational upper bound).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteSectorRectangularVariational.re_sum_inner_map_le_ky_fan_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/FiniteSectorRectangularVariational.re_sum_inner_map_le_ky_fan_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every pair of orthonormal k-families has real paired trace at most the Ky Fan sum. The proof passes through positive square roots, polar structure and a self-adjoint zero extension; the rectangular estimate does not assume equal dimensions.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteSectorRectangularVariational.kyFanSum`
- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteSectorRectangularVariational.re_sum_inner_map_le_ky_fan_sum`
- Dependency: [D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse](../../Observer/Hilbert/FiniteMoorePenroseInverse.md)
- Dependency: [D5/S3/Quantum/Entanglement/FiniteSectorChannelModel](FiniteSectorChannelModel.md)
