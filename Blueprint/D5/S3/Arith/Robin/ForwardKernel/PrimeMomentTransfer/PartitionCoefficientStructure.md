# Quadratic partition coefficients

## Abstract

Structural restrictions on nonzero quadratic collision configurations.

**Definition 1.1 (Reduction coefficient of a configuration).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure.partitionCoefficient`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure.partitionCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a partition sigma of Fin k, retained subset S of its blocks, and real a and b, partitionCoefficient is the product of u(size(B)) over retained blocks B times the product of v(size(B)) over the other blocks, where u and v are the quadratic power coefficients.

**Definition 1.2 (Residual after removing free-block collisions).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure.partitionMainResidual`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure.partitionMainResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite index type, commutative real algebra A, linear functional ell, algebra-valued family Y, and original scalar weight family f, partitionMainResidual is the product of the scalar sums of the free block weights times the ordered distinct-index moment of the retained block weights. The retained blocks are enumerated by the inverse of equivFin on S.

**Theorem 1.3 (Free singletons vanish).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure.partitionCoefficient_zero_of_free_singleton`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure.partitionCoefficient_zero_of_free_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a block outside the retained set S has multiplicity one, partitionCoefficient is zero, since the constant coordinate v(1) is zero.

**Theorem 1.4 (Every nonzero free block has size at least two).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure.partitionCoefficient_nonzero_free_mult`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure.partitionCoefficient_nonzero_free_mult` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If partitionCoefficient is nonzero, every unretained block has multiplicity at least two. Every quotient block is nonempty, and multiplicity one would force the coefficient to vanish.

**Theorem 1.5 (No error when every block is retained).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure.kernelDistinctMoment_eq_main_of_compl_card_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure.kernelDistinctMoment_eq_main_of_compl_card_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the complement of S has cardinality zero, kernelDistinctMoment equals partitionMainResidual exactly. There are then no collision edges involving an unretained block, so only the empty edge set occurs in the collision expansion. The statement includes the top-order distinct-index moment and requires no size estimate for it.

**Theorem 1.6 (A single retained block is centered).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure.kernelDistinctMoment_zero_of_retained_card_one`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure.kernelDistinctMoment_zero_of_retained_card_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If ell(Y(d))=0 for every index d and the retained set S has cardinality one, kernelDistinctMoment is zero. Every summand contains exactly one centered algebra factor inside ell.

**Theorem 1.7 (The corresponding main residual is centered).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure.partitionMainResidual_zero_of_retained_card_one`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure.partitionMainResidual_zero_of_retained_card_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same centering and cardinality-one condition on S, partitionMainResidual is zero. Its empty-edge assignment representation again contains one centered algebra factor in each summand.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure.kernelDistinctMoment_eq_main_of_compl_card_zero`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure.kernelDistinctMoment_zero_of_retained_card_one`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure.partitionCoefficient`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure.partitionCoefficient_nonzero_free_mult`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure.partitionCoefficient_zero_of_free_singleton`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure.partitionMainResidual`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure.partitionMainResidual_zero_of_retained_card_one`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion](PartitionCollisionExpansion.md)
