# Conditional Record Capacity

## Abstract

Nonzero equivariant idempotent resolutions have bounded size: the commutant dimension always bounds them, and a supplied matrix-block decomposition improves this to the sum of the block sizes.

A common finite complex matrix action U and equivariance of all records are explicit physical inputs. The statements do not impose a bound on arbitrary record structures. Self-adjoint records are included: the counting argument needs only nonzero idempotents summing to identity. No irreducible decomposition is inferred from the physical setup.

**Theorem 1.1 (The ranges exhaust the dimension budget).**

Lean statement: `D5/S3/Quantum/Matrix/RecordCapacity.sum_range_finrank_of_idempotent_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/RecordCapacity.sum_range_finrank_of_idempotent_sum` (`✓ std3`). ∎

*Citation.* Junyan Xu and the mathlib community (2026). *Wedderburn–Artin structure and trace of idempotent endomorphisms*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/SimpleModule/IsAlgClosed.lean>.

*Commentary.*

The trace of each idempotent is its range dimension. Summing and using the identity resolution gives the dimension of the carrier. The scalar field may be any field of characteristic zero.

**Theorem 1.2 (Each nonzero record consumes a dimension).**

Lean statement: `D5/S3/Quantum/Matrix/RecordCapacity.card_le_finrank_of_idempotent_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/RecordCapacity.card_le_finrank_of_idempotent_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A zero range dimension would make the trace and hence the idempotent zero. Summing the positive integer range dimensions bounds the count.

**Theorem 1.3 (The dimension of a complex algebra bounds its resolutions).**

Lean statement: `D5/S3/Quantum/Matrix/RecordCapacity.algebra_card_le_finrank`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/RecordCapacity.algebra_card_le_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Left multiplication represents the algebra faithfully on itself. The preceding count therefore applies in its complex dimension.

**Theorem 1.4 (The commutant bounds equivariant records).**

Lean statement: `D5/S3/Quantum/Matrix/RecordCapacity.equivariant_record_card_le_commutant_finrank`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/RecordCapacity.equivariant_record_card_le_commutant_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equivariance places each record in the actual centralizer of the common action. Its left regular action gives the bound by its complex dimension. This is weaker than the multiplicity-sum law in general.

**Theorem 1.5 (Matrix blocks give the sum of their sizes).**

Lean statement: `D5/S3/Quantum/Matrix/RecordCapacity.matrix_blocks_card_le_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/RecordCapacity.matrix_blocks_card_le_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product of matrix algebras acts faithfully by block diagonal matrices on a carrier whose dimension is the sum of the block sizes. The count applies on this smaller carrier.

**Theorem 1.6 (A supplied commutant decomposition gives the sharp bound).**

Lean statement: `D5/S3/Quantum/Matrix/RecordCapacity.equivariant_record_card_le_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/RecordCapacity.equivariant_record_card_le_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The algebra equivalence is an explicit hypothesis linking the actual commutant to the stated blocks. Transport each record through it and apply the block count. Identifying these sizes with multiplicities of a separately specified irrep decomposition is not formalized here.

**Theorem 1.7 (Semisimplicity supplies one bound for all resolutions).**

Lean statement: `D5/S3/Quantum/Matrix/RecordCapacity.semisimple_commutant_has_record_capacity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/RecordCapacity.semisimple_commutant_has_record_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The upstream Wedderburn–Artin theorem supplies block sizes for a semisimple commutant. Those same sizes bound every finite nonzero equivariant orthogonal resolution. Semisimplicity is an assumption.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/RecordCapacity.algebra_card_le_finrank`
- Truth anchor: `D5/S3/Quantum/Matrix/RecordCapacity.card_le_finrank_of_idempotent_sum`
- Truth anchor: `D5/S3/Quantum/Matrix/RecordCapacity.equivariant_record_card_le_commutant_finrank`
- Truth anchor: `D5/S3/Quantum/Matrix/RecordCapacity.equivariant_record_card_le_sum`
- Truth anchor: `D5/S3/Quantum/Matrix/RecordCapacity.matrix_blocks_card_le_sum`
- Truth anchor: `D5/S3/Quantum/Matrix/RecordCapacity.semisimple_commutant_has_record_capacity`
- Truth anchor: `D5/S3/Quantum/Matrix/RecordCapacity.sum_range_finrank_of_idempotent_sum`
