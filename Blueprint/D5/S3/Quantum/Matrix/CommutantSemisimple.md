# Semisimple Unitary Commutants

## Abstract

A finite-dimensional unitary group action has a semisimple commutant. An integer shear action has a nonzero Jacobson radical, showing why the unitary hypothesis matters.

The group is arbitrary: neither finiteness nor compactness is required. The matrices have a finite index type and complex entries. The commutant is the complex subalgebra of matrices commuting with every matrix in the supplied representation.

**Theorem 1.1 (Adjoint closure forces a zero radical).**

Lean statement: `D5/S3/Quantum/Matrix/CommutantSemisimple.jacobson_eq_bot_of_conjTranspose_closed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CommutantSemisimple.jacobson_eq_bot_of_conjTranspose_closed` (`✓ std3`). ∎

*Citation.* The mathlib community (2026). *Artinian Jacobson radicals and the positive matrix trace pairing*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/Artinian/Module.lean>.

*Commentary.*

Let A be a unital complex matrix subalgebra closed under conjugate transpose. It is finite dimensional, so its Jacobson radical is a nilpotent ideal. For X in that radical, the product of the adjoint of X with X is again in the radical. Its trace is zero by nilpotence. The positive trace pairing then forces X to be zero.

**Theorem 1.2 (Unitary commutants are closed under adjoints).**

Lean statement: `D5/S3/Quantum/Matrix/CommutantSemisimple.commutant_conjTranspose_mem_of_unitary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CommutantSemisimple.commutant_conjTranspose_mem_of_unitary` (`✓ std3`). ∎

*Citation.* The mathlib community (2026). *Artinian Jacobson radicals and the positive matrix trace pairing*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/Artinian/Module.lean>.

*Commentary.*

The adjoint of the matrix representing g is the matrix representing its inverse. Thus the image of the representation is closed under adjoints, and so is its centralizer.

**Theorem 1.3 (Unitarity implies semisimplicity).**

Lean statement: `D5/S3/Quantum/Matrix/CommutantSemisimple.commutant_isSemisimpleRing_of_unitary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CommutantSemisimple.commutant_isSemisimpleRing_of_unitary` (`✓ std3`). ∎

*Citation.* The mathlib community (2026). *Artinian Jacobson radicals and the positive matrix trace pairing*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/Artinian/Module.lean>.

*Commentary.*

Apply the zero-radical theorem to the commutant. An Artinian ring with zero Jacobson radical is semisimple. No group average or integral is involved.

**Theorem 1.4 (One block-size bound for every equivariant record resolution).**

Lean statement: `D5/S3/Quantum/Matrix/CommutantSemisimple.unitary_commutant_has_record_capacity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CommutantSemisimple.unitary_commutant_has_record_capacity` (`✓ std3`). ∎

*Citation.* The mathlib community (2026). *Artinian Jacobson radicals and the positive matrix trace pairing*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/Artinian/Module.lean>.

*Commentary.*

The semisimple complex commutant admits a product decomposition into full matrix algebras with nonzero block sizes. The sum of those sizes bounds every finite family of nonzero equivariant orthogonal idempotents summing to identity. Semisimplicity follows from unitarity here.

**Theorem 1.5 (The integer shear commutant).**

Lean statement: `D5/S3/Quantum/Matrix/CommutantSemisimple.unipotent_commutant_characterization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CommutantSemisimple.unipotent_commutant_characterization` (`✓ std3`). ∎

*Citation.* The mathlib community (2026). *Artinian Jacobson radicals and the positive matrix trace pairing*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/Artinian/Module.lean>.

*Commentary.*

The integer z acts by the matrix with rows (1,z) and (0,1). An arbitrary complex two-by-two matrix commutes with every such shear exactly when it has rows (a,b) and (0,a), for complex a and b.

**Theorem 1.6 (The upper-right matrix unit belongs to the radical).**

Lean statement: `D5/S3/Quantum/Matrix/CommutantSemisimple.unipotent_radical_element_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CommutantSemisimple.unipotent_radical_element_mem` (`✓ std3`). ∎

*Citation.* The mathlib community (2026). *Artinian Jacobson radicals and the positive matrix trace pairing*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/Artinian/Module.lean>.

*Commentary.*

Let E have upper-right entry one and all other entries zero. For every element Y of the shear commutant, one minus Y times E is a left inverse of one plus Y times E. The Jacobson membership criterion puts E in the radical.

**Theorem 1.7 (The radical element is nonzero).**

Lean statement: `D5/S3/Quantum/Matrix/CommutantSemisimple.unipotent_radical_element_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CommutantSemisimple.unipotent_radical_element_ne_zero` (`✓ std3`). ∎

*Citation.* The mathlib community (2026). *Artinian Jacobson radicals and the positive matrix trace pairing*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/Artinian/Module.lean>.

*Commentary.*

The upper-right entry of E is one. Its inclusion in the commutant is injective, so E is nonzero as an element of that algebra.

**Theorem 1.8 (The shear commutant is not semisimple).**

Lean statement: `D5/S3/Quantum/Matrix/CommutantSemisimple.unipotent_commutant_not_isSemisimpleRing`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CommutantSemisimple.unipotent_commutant_not_isSemisimpleRing` (`✓ std3`). ∎

*Citation.* The mathlib community (2026). *Artinian Jacobson radicals and the positive matrix trace pairing*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/Artinian/Module.lean>.

*Commentary.*

A semisimple ring has zero Jacobson radical. The shear commutant contains the nonzero radical element E, so it is not semisimple. This integer representation disproves the claim obtained by omitting unitarity.

**Theorem 1.9 (Universal semisimplicity without unitarity is false).**

Lean statement: `D5/S3/Quantum/Matrix/CommutantSemisimple.not_all_integer_matrix_commutants_semisimple`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CommutantSemisimple.not_all_integer_matrix_commutants_semisimple` (`✓ std3`). ∎

*Citation.* The mathlib community (2026). *Artinian Jacobson radicals and the positive matrix trace pairing*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/Artinian/Module.lean>.

*Commentary.*

The claim that every complex two-dimensional integer representation has a semisimple commutant is false: apply it to the shear representation and its nonzero radical gives a contradiction.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/CommutantSemisimple.commutant_conjTranspose_mem_of_unitary`
- Truth anchor: `D5/S3/Quantum/Matrix/CommutantSemisimple.commutant_isSemisimpleRing_of_unitary`
- Truth anchor: `D5/S3/Quantum/Matrix/CommutantSemisimple.jacobson_eq_bot_of_conjTranspose_closed`
- Truth anchor: `D5/S3/Quantum/Matrix/CommutantSemisimple.not_all_integer_matrix_commutants_semisimple`
- Truth anchor: `D5/S3/Quantum/Matrix/CommutantSemisimple.unipotent_commutant_characterization`
- Truth anchor: `D5/S3/Quantum/Matrix/CommutantSemisimple.unipotent_commutant_not_isSemisimpleRing`
- Truth anchor: `D5/S3/Quantum/Matrix/CommutantSemisimple.unipotent_radical_element_mem`
- Truth anchor: `D5/S3/Quantum/Matrix/CommutantSemisimple.unipotent_radical_element_ne_zero`
- Truth anchor: `D5/S3/Quantum/Matrix/CommutantSemisimple.unitary_commutant_has_record_capacity`
- Dependency: [D5/S3/Quantum/Matrix/RecordCapacity](RecordCapacity.md)
