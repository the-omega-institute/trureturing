# Faces and connected compatible partitions

## Abstract

Connected compatible partitions recover the actual geometric faces.

These recovery statements implement the classical correspondence cited as source Theorem 3.1, attributed there to Stanley. Their formal set/partition constructions are repository-derived.

**Theorem 1.1 (The constructed face recovers its partition).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCCP.crownPartitionFace_tightComponent_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCCP.crownPartitionFace_tightComponent_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For every connected compatible partition of the augmented crown vertices, two vertices are reachable in the tight graph of its constructed face exactly when they belong to the same partition block. Connectedness and quotient-order antisymmetry are explicit fields of the partition.

**Theorem 1.2 (Recovery of every exposed face).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCCP.crownPartitionFace_crownFacePartition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCCP.crownPartitionFace_crownFacePartition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For every actual exposed face, forming its tight-component partition and then imposing the partition equalities recovers the same face. Together with the reverse recovery this gives the geometric correspondence used for counting. Endpoint separation characterizes nonempty faces.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCCP.crownPartitionFace_crownFacePartition`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCCP.crownPartitionFace_tightComponent_iff`
- Dependency: [D5/S3/Combinatorics/Geometry/CrownOrderPolytope](CrownOrderPolytope.md)
