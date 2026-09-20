# Affine dimensions of crown faces

## Abstract

The number of partition blocks determines the actual affine dimension.

This is the dimension clause of the classical face/partition correspondence cited in source Theorem 3.1.

**Theorem 1.1 (Dimension equals the number of blocks minus two).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeDimension.crownPartitionFace_finrank_direction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeDimension.crownPartitionFace_finrank_direction` (`✓ std3`). ∎

*Citation.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For any connected compatible partition whose bottom and top blocks differ, the real dimension of the direction of the affine span of its face equals the cardinality of its quotient minus two. The two endpoint blocks have fixed coordinate values; the other block coordinates supply the independent directions.

**Theorem 1.2 (Dimension of any nonempty exposed face).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeDimension.crownExposedFace_finrank_direction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeDimension.crownExposedFace_finrank_direction` (`✓ std3`). ∎

*Citation.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For every nonempty actual exposed face, its real affine dimension equals the number of blocks of its tight-component partition minus two. This transports the constructed-face dimension theorem through geometric face recovery.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeDimension.crownExposedFace_finrank_direction`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeDimension.crownPartitionFace_finrank_direction`
- Dependency: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCCP](CrownOrderPolytopeCCP.md)
