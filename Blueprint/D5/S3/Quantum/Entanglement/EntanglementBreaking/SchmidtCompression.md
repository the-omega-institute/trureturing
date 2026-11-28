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

For 1 ≤ k ≤ d, the Schmidt-restricted bound controls every unit vector in the compression of the candidate to an isometric k-dimensional input subspace. The contraction-block separability theorem applies to the shifted compression.

**Theorem 1.3 (The map defined by the Choi candidate is k-entanglement-breaking).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SchmidtCompression.candidate_isKEB`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/SchmidtCompression.candidate_isKEB` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 1 ≤ k ≤ d and Hermitian H satisfying the Schmidt-restricted quadratic bound, the map with input-first Choi matrix I − (16/d)H is k-entanglement-breaking. A right isometric factorization transfers separability from the isometric compression to every rectangular local congruence.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SchmidtCompression.SchmidtQuadraticBound`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SchmidtCompression.candidate_compression_separable`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SchmidtCompression.candidate_isKEB`
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/ContractionBlocks](../AbsoluteSeparability/ContractionBlocks.md)
- Dependency: [D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace](PPTTrace.md)
- Dependency: [D5/S3/Quantum/Entanglement/EntanglementBreaking/RightIsometry](RightIsometry.md)
- Dependency: [D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation](../WitnessKernelTraceCriteriaRefutation.md)
