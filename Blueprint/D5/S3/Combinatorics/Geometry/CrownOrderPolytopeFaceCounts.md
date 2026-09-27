# Actual geometric face counts

## Abstract

The enumeration counts real exposed faces by affine dimension.

The count has the geometric meaning of source Section 2; the formula is Theorem 3.6. The signed lower binomial index is implemented by an explicit zero guard before natural subtraction.

**Definition 1.1 (Geometric definition of the count).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeFaceCounts.crownGeometricFaceCount`

*Formalization.* `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeFaceCounts.crownGeometricFaceCount` (`✓ std3`).

*Citation.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For natural n and d, the count is the natural cardinality of actual nonempty exposed faces of the real crown order polytope whose affine-span direction has real dimension d. This definition is independent of the enumerative sum.

**Theorem 1.2 (The face formula for n at least two).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeFaceCounts.crownGeometricFaceCount_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeFaceCounts.crownGeometricFaceCount_eq` (`✓ std3`). ∎

*Citation.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For every n at least two and every natural dimension d, the geometric count equals the exact selected-block sum with two additional vertices and one additional edge. The proof uses the face/partition correspondence, its affine dimension formula, endpoint recovery, parity-profile counts and the exceptional partitions. This formalizes the published face-count formula rather than assuming it.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeFaceCounts.crownGeometricFaceCount`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeFaceCounts.crownGeometricFaceCount_eq`
- Dependency: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeDimension](CrownOrderPolytopeDimension.md)
- Dependency: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeSelectionCounts](CrownOrderPolytopeSelectionCounts.md)
- Dependency: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeTwoExceptions](CrownOrderPolytopeTwoExceptions.md)
