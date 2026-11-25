# Joint POVM transport through the occupied subspace

## Abstract

A rectangular partial isometry preserves the full set of finite POVM scores.

**Theorem 1.1 (Partial-isometry transport preserves all attainable scores).**

Lean statement: `D5/S3/Quantum/PureState/JointRecordTransport.success_set_partialIsometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/JointRecordTransport.success_set_partialIsometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the finite label type be nonempty, let p be any real weight function, and let the input and output states be density states on finite complex carriers. For a rectangular matrix V, assume V(V†V) = V, that V†V acts as the identity on each input density matrix by left multiplication, and that each output density matrix is V rho V†.

Compress each POVM effect and assign the complementary projector to one fixed label. The complement contributes zero to every state trace. Compressing in both directions gives equality of the attainable success sets.

**Theorem 1.2 (Transport on pure amplitudes preserves the success set).**

Lean statement: `D5/S3/Quantum/PureState/JointRecordTransport.success_set_pure_partialIsometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/JointRecordTransport.success_set_pure_partialIsometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source and target amplitudes have squared norm one for each label. The same partial-isometry identity is assumed, V†V fixes each source amplitude, and V maps it to the corresponding target amplitude. Rank-one density matrices then satisfy the matrix transport hypotheses. The binary product proof uses this equality to carry an attainable score to the original carrier.

## References

- Truth anchor: `D5/S3/Quantum/PureState/JointRecordTransport.success_set_partialIsometry`
- Truth anchor: `D5/S3/Quantum/PureState/JointRecordTransport.success_set_pure_partialIsometry`
- Dependency: [D5/S3/Quantum/PureState/JointRecordDecoding](JointRecordDecoding.md)
