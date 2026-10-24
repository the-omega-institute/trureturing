# Invariant Forms and Scalar Commutants

## Abstract

Invariant Forms and Scalar Commutants

Let k be any field, Gamma any group, and V a finite dimensional k-vector space. Fix a representation rho and a nonzero nondegenerate invariant bilinear form B. Every invariant bilinear form C, including zero, is a unique scalar multiple of B when every endomorphism commuting with rho is scalar. Algebraic closedness is not required: the scalar-commutant property is an explicit premise.

Mathlib provides symmCompOfNondegenerate and its pairing identity. The new argument proves this comparison endomorphism commutes with rho: invariance moves the action in the second slot through the inverse group element. The supplied scalar commutant then gives proportionality. Nonzero B gives uniqueness by scalar cancellation. This is the classical Schur and duality argument; no literature novelty is claimed.

Library-first search at Mathlib pin 56a005855ea17e0b0958f73ec801ae140b0a1679 checked RepresentationTheory/Irreducible, Intertwining and LinearAlgebra/BilinearForm. Irreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed and finrank_intertwiningMap_self concern endomorphism intertwiners, and do not provide the invariant-form comparison. They are not reproved. The actual lattice consumer reuses OperatorAlgebra.actual_operator_algebra and its scalar_commutant field.

The private original-ground comparison in ActualChosenFormSymmetry is a live consumer. The theorem adds the missing equivariance argument rather than a new application of Schur endomorphism results. The full arbitrary-field and universe-polymorphic information-escape registration remains unfinished; see https://github.com/the-omega-institute/trureturing/issues/21214.

**Theorem 1.1 (Invariant Forms and Scalar Commutants).**

Lean statement: `D5/S3/Quantum/Algebra/InvariantFormProportionality.invariant_forms_proportional_of_scalar_commutant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/InvariantFormProportionality.invariant_forms_proportional_of_scalar_commutant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be any field, Gamma any group, and V a finite dimensional k-vector space. Fix a representation rho and a nonzero nondegenerate invariant bilinear form B. Every invariant bilinear form C, including zero, is a unique scalar multiple of B when every endomorphism commuting with rho is scalar. Algebraic closedness is not required: the scalar-commutant property is an explicit premise.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/InvariantFormProportionality.invariant_forms_proportional_of_scalar_commutant`
