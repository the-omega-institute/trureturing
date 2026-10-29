# Original signed four-current finite recurrence

## Abstract

Original signed four-current finite recurrence.

**Definition 1.1 (Unpaired labeled slots).**

Lean statement: `D5/S3/VertexAlgebra/Characters/FourCurrent/TraceRecurrence.unpaired`

*Formalization.* `D5/S3/VertexAlgebra/Characters/FourCurrent/TraceRecurrence.unpaired` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each of the ten labeled partial matchings, PM4.unpaired is the subset of Fin 4 whose slots are neither endpoint of any edge. The original definition is used directly by the matching-mode compatibility, charge weights and channel proof.

**Theorem 1.2 (Original signed four-current finite recurrence).**

Lean statement: `D5/S3/VertexAlgebra/Characters/FourCurrent/TraceRecurrence.original_four_finite_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/FourCurrent/TraceRecurrence.original_four_finite_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original lattice D with positive-definite real Gram matrix, labels i : Fin 4 → Fin D.rank and natural grades n : Fin 4 → Nat with n(0) < n(1), put ell=n(1)-n(0), p=n(2)-n(1), q=n(3)-n(2), r=n(0)-n(3), with the latter differences in the integers. The literal original four-block trace is the sum over a=0,...,floor(n(0)/ell) of the three labeled CCR contractions times the corresponding original two-mode word trace at the signed grade n(0)-a ell. The factors are ell times the signed Gram entry when the contracted modes sum to zero, and zero otherwise.

The module owns the literal original complete-grade trace, all ten labeled matchings and their bounded coefficient, zero-mode basis trace, signed homogeneity and rectangular finite trace cyclicity. Original positive energy kills every negative grade. The signed four-current commutator and finite telescoping proof are used by the matching-mode coefficient reduction; they impose no substitute CCR or trace assumption. Zero and equal grades, repeated labels, signed Gram entries and rank zero remain part of the definitions and of the subsequent endpoint.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Characters/FourCurrent/TraceRecurrence.original_four_finite_sum`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/FourCurrent/TraceRecurrence.unpaired`
- Dependency: [D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentTrace](../LatticeTwoCurrentTrace.md)
- Dependency: [D5/S3/VertexAlgebra/Energy/LatticeCoefficientEnergy](../../Energy/LatticeCoefficientEnergy.md)
