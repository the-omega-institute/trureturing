# Compatibility of crown cycle partitions

## Abstract

Odd block parity characterizes nontrivial compatible cycle partitions.

The first characterization is source Lemma 3.2. The endpoint-isolated formulation is an implementation consequence used in recovering augmented partitions.

**Theorem 1.1 (Compatibility exactly when an odd block exists).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCyclePartitions.crownCycleCompatible_iff_exists_oddBlock`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCyclePartitions.crownCycleCompatible_iff_exists_oddBlock` (`✓ std3`). ∎

*Citation.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For n at least two and a nontrivial connected partition of the 2n-cycle, antisymmetry of the induced crown quotient order is equivalent to existence of a block with odd cardinality. The nontriviality hypothesis excludes the one-block case.

**Theorem 1.2 (Odd blocks when both endpoints are isolated).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCyclePartitions.crownPartition_exists_oddOriginalBlock`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCyclePartitions.crownPartition_exists_oddOriginalBlock` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For an augmented connected compatible partition at n at least two, if neither endpoint meets an original vertex and the original-vertex partition is nontrivial, there exists an odd original block distinct from both endpoint blocks.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCyclePartitions.crownCycleCompatible_iff_exists_oddBlock`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCyclePartitions.crownPartition_exists_oddOriginalBlock`
- Dependency: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCycleCuts](CrownOrderPolytopeCycleCuts.md)
