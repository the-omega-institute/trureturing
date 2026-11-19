# Projection bounds at the Wu endpoint

## Abstract

Trace pairing with the signed map is bounded on rank-one and mixed rank projections.

The unweighted twirl fixes total measured mass, and the Pauli frame bounds control sums over the first and last degree levels. The projection onto the first two vectors of a basis and its orthogonal complement resolve the identity. The decreasing conjugation weights combine with the resulting prefix bounds.

For any two unit vectors u and v, the real trace of the product of the projector onto u and the image of the projector onto v lies between β² and α² (`A₁_rankOne_rankOne`).

For any unit vector u and any orthonormal basis of the two-mode space, the real trace pairing of the projector onto u with the image of the sum of the first two basis projectors is at most α (`A₁_rankOne_rankTwo_basis`).

**Theorem 1.1 (Resolution of the identity).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointProjectionBounds.sum_endpointProjector`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuEndpointProjectionBounds.sum_endpointProjector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four projectors of an orthonormal basis sum to the identity.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointProjectionBounds.sum_endpointProjector`
- Dependency: [D5/S3/Quantum/Semigroups/WuEndpointWeightedPauli](WuEndpointWeightedPauli.md)
