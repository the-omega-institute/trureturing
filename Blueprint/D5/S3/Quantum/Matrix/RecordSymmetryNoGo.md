# Equivariant Record Symmetry No-Go

## Abstract

Equivariant Hermitian idempotents are trivial under irreducible symmetry.

**Theorem 1.1 (Idempotent no-go).**

$equivariantIdempotentZeroOrOne$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/RecordSymmetryNoGo.equivariant_selfAdjoint_idempotent_eq_zero_or_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Schur scalarity followed by the scalar equation r squared equals r gives the two values.

**Theorem 1.2 (Reverse obstruction).**

$nontrivialIdempotentImpliesReducible$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/RecordSymmetryNoGo.nontrivial_equivariant_selfAdjoint_idempotent_implies_reducible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the contrapositive of the idempotent no-go.

**Theorem 1.3 (Two-record consequence).**

$twoRecordsImplyReducible$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/RecordSymmetryNoGo.two_nonzero_orthogonal_equivariant_records_imply_reducible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first projection must be identity under irreducibility, and orthogonality then kills the second.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/RecordSymmetryNoGo.equivariant_selfAdjoint_idempotent_eq_zero_or_one`
- Truth anchor: `D5/S3/Quantum/Matrix/RecordSymmetryNoGo.nontrivial_equivariant_selfAdjoint_idempotent_implies_reducible`
- Truth anchor: `D5/S3/Quantum/Matrix/RecordSymmetryNoGo.two_nonzero_orthogonal_equivariant_records_imply_reducible`
- Dependency: [D5/S3/Quantum/Matrix/CrossSpeciesConsensus](CrossSpeciesConsensus.md)
