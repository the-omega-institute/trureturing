# The closed polar-sum identity for adapted DPS

## Abstract

The closed polar-sum identity for adapted DPS

The real space is the existing HermitianMat space with its trace inner product. No unclosed dual-sum equality or unrestricted exact dual-certificate lifting is asserted. This is the closure-preserving application in the note by Haobo Ma and Wenlin Zhang.

**Definition 1.1 (ordinaryCone).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDual.ordinaryCone`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDual.ordinaryCone` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual ordinary DPS cone is represented as a closed convex cone in the real Hermitian space. Its defining lifts, cuts, and unnormalized marginals are unchanged.

**Definition 1.2 (boseSubspace).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDual.boseSubspace`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDual.boseSubspace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the full real linear space of Hermitian operators fixed by the actual pair-symmetric-projector sandwich. Positivity is supplied by DPS, not included in the subspace definition.

**Theorem 1.3 (closed dual identity).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDual.closed_dual_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDual.closed_dual_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polar of the actual adapted DPS cone is the closure of the sum of the ordinary DPS polar and the orthogonal complement of the Bose support subspace. The proof applies finite-dimensional bipolarity to the closed conic sum and uses actual ordinary DPS closedness. The closure remains part of the conclusion.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDual.boseSubspace`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDual.closed_dual_identity`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDual.ordinaryCone`
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS](BoseDPS.md)
