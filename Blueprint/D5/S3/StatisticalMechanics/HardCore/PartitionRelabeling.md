# PartitionRelabeling

## Abstract

Exact correspondence between grid geometry and actual independent-set messages.

**Theorem 1.1 (Exact independent configurations).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/PartitionRelabeling.independent_image_iff`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/PartitionRelabeling.independent_image_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adjacency preservation and reflection transport independence in both directions. The source and target use the existing actual independent-set predicate.

**Theorem 1.2 (A bijection of the complete configuration families).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/PartitionRelabeling.configurations_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/PartitionRelabeling.configurations_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse image under the vertex equivalence supplies surjectivity. Equality is at the configuration-set level, before counting or weighting.

**Theorem 1.3 (Transport every vertex weight).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/PartitionRelabeling.partition_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/PartitionRelabeling.partition_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the transported configuration weights gives an exact commutative-semiring identity, including polynomial and complex activities.

**Theorem 1.4 (Transport a marked deletion).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/PartitionRelabeling.image_erase_equiv`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/PartitionRelabeling.image_erase_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same relabeling carries the marked numerator domain and the full denominator domain. No cancellation or nonzero assumption occurs.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/PartitionRelabeling.configurations_relabel`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/PartitionRelabeling.image_erase_equiv`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/PartitionRelabeling.independent_image_iff`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/PartitionRelabeling.partition_relabel`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion](IndependentPartitionDeletion.md)
