# Partial transpose of a finite Hermitian sign matrix

## Abstract

Output partial transpose preserves the Hermitian sign matrix distribution.

**Definition 1.1 (Boolean transformation for output partial transpose).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.ptBitTransform`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.ptBitTransform` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The output index swap transports each upper entry. If the order reverses, the imaginary sign is complemented and the real sign is preserved. The diagonal and unused lower coordinates are fixed.

**Theorem 1.2 (Fixed-vector tail after partial transpose).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.signCubeSample_partialTranspose_quadratic_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.signCubeSample_partialTranspose_quadratic_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Boolean transformation is an involution and preserves uniform measure. Entrywise equality transfers the original quadratic tail with the same constants.

**Definition 1.3 (Ptindex).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.PTIndex`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.PTIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input and output indices for the square bipartite matrix are a pair in Fin d times Fin d.

**Definition 1.4 (Pt lt).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.ptLt`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.ptLt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Order the pairs by their images under the standard Fin product equivalence.

**Definition 1.5 (Pt lt decidable).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.ptLt_decidable`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.ptLt_decidable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Decide this comparison in the resulting finite linear order.

**Definition 1.6 (Pt cross).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.ptCross`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.ptCross` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exchange the output coordinates between the two product indices while holding their input coordinates fixed.

**Theorem 1.7 (Partial transpose sign cube sample).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.partialTranspose_signCubeSample`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.partialTranspose_signCubeSample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking the output partial transpose of the sample equals evaluating the sample at the transformed Boolean assignment.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.PTIndex`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.partialTranspose_signCubeSample`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.ptBitTransform`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.ptCross`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.ptLt`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.ptLt_decidable`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose.signCubeSample_partialTranspose_quadratic_tail`
- Dependency: [D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixNetBounds](SignMatrixNetBounds.md)
