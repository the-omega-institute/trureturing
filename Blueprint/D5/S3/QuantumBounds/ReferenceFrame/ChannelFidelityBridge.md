# Finite Channel-to-Fidelity Bridge

## Abstract

A finite excitation-exchange permutation gives a unitary, a Kraus family, and an exact bridge from entanglement fidelity to the frozen nearest-neighbour quadratic form.

The system has two basis states and the reference has N levels. The joint basis permutation exchanges one excitation between them whenever the reference is away from the corresponding boundary, and fixes the two unmatched boundary vectors. All matrices and sums in this document are finite-dimensional.

**Theorem 1.1 (The excitation-exchange matrix is unitary).**

$$U^{*} U = I$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrame/ChannelFidelityBridge.exchange_unitary_is_unitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exchange matrix is the permutation matrix of an involution on the joint computational basis. Mathlib's conjugate-transpose and permutation-matrix multiplication identities therefore reduce the unitarity law to the inverse law of that permutation.

**Theorem 1.2 (Exchange preserves total excitation).**

$$n(exchange(x)) = n(x)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrame/ChannelFidelityBridge.exchange_basis_preserves_total_excitation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an interior transition the system excitation changes by one while the reference excitation changes by the opposite amount. At an unmatched boundary the basis label is fixed. The total grading is consequently unchanged in every branch.

**Definition 1.3 (The reduced system map is a finite Kraus sum).**

Lean statement: `D5/S3/QuantumBounds/ReferenceFrame/ChannelFidelityBridge.exchangeChannel`

*Formalization.* `D5/S3/QuantumBounds/ReferenceFrame/ChannelFidelityBridge.exchangeChannel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Projecting the reference output onto each level r gives one matrix K_r. The reduced system map sends rho to the finite sum of K_r rho K_r star. This module introduces only this concrete family and does not add a general channel library.

**Theorem 1.4 (Entanglement fidelity is the frozen quadratic form).**

$$F_{e}(c) = Q_{N}(c)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrame/ChannelFidelityBridge.entanglement_fidelity_eq_nearest_neighbor_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Entanglement fidelity is defined by the finite trace expression one quarter times the sum of the squared trace magnitudes against the ideal bit flip. Computing the two off-diagonal Kraus entries leaves exactly the two zero-boundary neighbouring reference amplitudes. The resulting sum is definitionally the existing nearestNeighborQuadratic; that quadratic is imported and is not redefined here.

**Theorem 1.5 (Entanglement fidelity is the squared averaging norm).**

$$F_{e}(c) = \lvert Jc\rvert_{2}^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrame/ChannelFidelityBridge.entanglement_fidelity_eq_average_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here J is zero-boundary nearest-neighbour averaging. This restates the same compiled bridge as a squared Euclidean norm and is the exact input needed by the finite path-spectrum module.

## References

- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrame/ChannelFidelityBridge.entanglement_fidelity_eq_average_norm_sq`
- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrame/ChannelFidelityBridge.entanglement_fidelity_eq_nearest_neighbor_quadratic`
- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrame/ChannelFidelityBridge.exchangeChannel`
- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrame/ChannelFidelityBridge.exchange_basis_preserves_total_excitation`
- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrame/ChannelFidelityBridge.exchange_unitary_is_unitary`
- Dependency: [D5/S3/QuantumBounds/ReferenceFrameTax](../ReferenceFrameTax.md)
