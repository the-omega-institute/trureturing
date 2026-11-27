# Separable Schmidt compressions

## Abstract

Schmidt-restricted quadratic bounds imply separable Choi compressions.

**Definition 1.1 (Schmidt-restricted quadratic form bound).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SchmidtCompression.SchmidtQuadraticBound`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/SchmidtCompression.SchmidtQuadraticBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The bound applies to unit Euclidean vectors whose coefficient matrices have rank at most k.

**Theorem 1.2 (Separability after rectangular input compression).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SchmidtCompression.candidate_compression_separable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/SchmidtCompression.candidate_compression_separable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A right isometric factorization reduces local congruence to an isometric compression followed by local filtering. The Schmidt-restricted bound controls every unit vector in the isometric compression. The contraction-block separability theorem applies to its scalar shift.

**Theorem 1.3 (Candidate is keb).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SchmidtCompression.candidate_isKEB`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/SchmidtCompression.candidate_isKEB` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For one at most k at most d, a Hermitian H satisfying the Schmidt-restricted quadratic bound gives a k-entanglement-breaking Choi candidate.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SchmidtCompression.SchmidtQuadraticBound`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SchmidtCompression.candidate_compression_separable`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SchmidtCompression.candidate_isKEB`
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/ContractionBlocks](../AbsoluteSeparability/ContractionBlocks.md)
- Dependency: [D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace](PPTTrace.md)
- Dependency: [D5/S3/Quantum/Entanglement/EntanglementBreaking/RightIsometry](RightIsometry.md)
- Dependency: [D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation](../WitnessKernelTraceCriteriaRefutation.md)
