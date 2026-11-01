# Physical Endpoint Marginals

## Abstract

Both physical endpoint partial traces of the compact target encoding agree with the corresponding ideal marginals for every logical matrix.

Let d assign a positive finite target rank to every logical sector. The compact target encoding places each logical sector in an orthogonal maximally entangled block of rank d(s). For an arbitrary complex logical matrix Y, encode it on the two physical target factors and trace either physical endpoint.

**Definition 1.1 (Encoded target matrix).**

Lean statement: `D5/S3/Quantum/PhysicalEndpointMarginal.encodedTarget`

*Formalization.* `D5/S3/Quantum/PhysicalEndpointMarginal.encodedTarget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The encoded matrix is targetEncoding(d) multiplied by Y and by the adjoint target encoding. This definition acts on every complex logical matrix.

**Definition 1.2 (Ideal endpoint marginal).**

Lean statement: `D5/S3/Quantum/PhysicalEndpointMarginal.targetMarginal`

*Formalization.* `D5/S3/Quantum/PhysicalEndpointMarginal.targetMarginal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ideal marginal is diagonal in the compact physical basis. At a coordinate x it equals the diagonal logical entry Y(s,s) divided by d(s) when the two physical coordinates agree, and is zero otherwise.

**Theorem 1.3 (Right endpoint identity).**

Lean statement: `D5/S3/Quantum/PhysicalEndpointMarginal.right_target_marginal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PhysicalEndpointMarginal.right_target_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Tracing the right physical factor of the encoded target matrix gives the ideal endpoint marginal on the left physical factor for every logical matrix.

**Theorem 1.4 (Left endpoint identity).**

Lean statement: `D5/S3/Quantum/PhysicalEndpointMarginal.left_target_marginal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PhysicalEndpointMarginal.left_target_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Tracing the left physical factor gives the same ideal marginal on the right physical factor for every logical matrix.

**Theorem 1.5 (Both physical endpoint identities).**

Lean statement: `D5/S3/Quantum/PhysicalEndpointMarginal.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PhysicalEndpointMarginal.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two endpoint identities hold together for every positive rank family and every complex logical matrix, including off-diagonal sector entries.

## References

- Truth anchor: `D5/S3/Quantum/PhysicalEndpointMarginal.encodedTarget`
- Truth anchor: `D5/S3/Quantum/PhysicalEndpointMarginal.left_target_marginal`
- Truth anchor: `D5/S3/Quantum/PhysicalEndpointMarginal.result`
- Truth anchor: `D5/S3/Quantum/PhysicalEndpointMarginal.right_target_marginal`
- Truth anchor: `D5/S3/Quantum/PhysicalEndpointMarginal.targetMarginal`
- Dependency: [D5/S3/Quantum/Entanglement/SectorSchmidtEncoding](Entanglement/SectorSchmidtEncoding.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](Information/PartialTraceMutualInformation.md)
