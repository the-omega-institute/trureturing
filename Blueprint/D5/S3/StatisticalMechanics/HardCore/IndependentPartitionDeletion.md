# Independent-set partition and deletion

## Abstract

The hard-core partition is a sum over Mathlib independent subsets of the actual finite domain.

**Definition 1.1 (Actual independent configurations).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.configurations`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.configurations` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Filter the powerset of the actual finite vertex domain using Mathlib IsIndepSet. The ambient graph can have infinitely many vertices.

**Definition 1.2 (Multivariate partition sum).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.partition`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.partition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum the product of the activities of the occupied vertices. This definition does not use a deletion recursion or an external count oracle.

**Definition 1.3 (Delete the closed neighborhood).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.closedComplement`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.closedComplement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Remove the root and its neighbors within the actual finite domain.

**Theorem 1.4 (Denominator-free deletion identity).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.partition_delete`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.partition_delete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Split independent configurations according to root occupancy. Insertion of the root is an injective map from configurations on the closed-complement domain. The resulting identity holds in every commutative semiring, including polynomial rings and complex numbers, without assuming any partition nonzero.

**Theorem 1.5 (Empty-domain normalization).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.partition_empty`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.partition_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The only configuration on the empty domain is the empty set, with weight one.

**Theorem 1.6 (Scalar evaluation preserves configurations).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.map_partition`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.map_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A semiring homomorphism changes the activities while preserving the exact family of independent sets.

**Definition 1.7 (The independence polynomial).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.independencePolynomial`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.independencePolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Assign the polynomial variable to every vertex in the weighted partition sum over integer polynomials.

**Theorem 1.8 (Complex evaluation is the actual partition).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.independencePolynomial_eval`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.independencePolynomial_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluation at a complex activity gives exactly the finite independent-set sum to which the deletion identity applies.

**Theorem 1.9 (Nonnegative real activities).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.one_le_partition`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.one_le_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All configuration weights are nonnegative and the empty configuration contributes one. This supplies the real-domain normalization used before complex continuation.

The deletion identity is classical. This source supplies the actual configuration semantics needed by the hard-core research lane. The proof scripts are logically reviewed candidates; Lean elaboration and Scribe emission have not been executed in the authoring runtime.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.closedComplement`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.configurations`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.independencePolynomial`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.independencePolynomial_eval`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.map_partition`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.one_le_partition`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.partition`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.partition_delete`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.partition_empty`
