# Adjoints of the Half-Current Normal Products

## Abstract

Hermitian adjoints for the original half-current normal products

**Theorem 1.1 (Normal-ordered pair).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockSugawaraHermitian.normalPair_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockSugawaraHermitian.normalPair_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Half-current adjoints reverse the two operators of a normal pair. The adjoint acts by the same normal pair at the reflected indices −j−1 and −k−1.

**Theorem 1.2 (Normal sum at opposite mode).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockSugawaraHermitian.normalSum_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockSugawaraHermitian.normalSum_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pointwise finite-support theorem writes each normal sum on a common finite interval containing both supports. The reflection j ↦ −j−1 permutes this interval. The normal-pair identity then gives the adjoint of the sum at the opposite mode.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockSugawaraHermitian.normalPair_adjoint`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockSugawaraHermitian.normalSum_adjoint`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockTensorHermitian](LatticeHalfFockTensorHermitian.md)
