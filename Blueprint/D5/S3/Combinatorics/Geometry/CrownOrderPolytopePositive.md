# All positive crown sizes

## Abstract

The actual two-vertex triangle completes the geometric formula.

The full-vector convention is the source Section 2 convention. The positive-size theorem completes the separate n equals one boundary, where the source cycle picture degenerates to a chain.

**Definition 1.1 (The full geometric f-vector).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopePositive.crownGeometricFVector`

*Formalization.* `D5/S3/Combinatorics/Geometry/CrownOrderPolytopePositive.crownGeometricFVector` (`✓ std3`).

*Citation.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For n, the vector has 2n+2 entries indexed by Fin(2n+2). Entry zero is one for the empty face; entry k greater than zero is the actual geometric count in dimension k-1. Its last entry includes the whole polytope.

**Theorem 1.2 (The formula for every positive size).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopePositive.crownGeometricFaceCount_eq_of_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopePositive.crownGeometricFaceCount_eq_of_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For every positive n and every natural dimension d, the same exact geometric face-count formula holds. At n equals one the augmented crown is a chain, and its actual faces are counted by consecutive cuts. This proves the triangle boundary independently of the n at least two cycle arguments.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopePositive.crownGeometricFVector`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopePositive.crownGeometricFaceCount_eq_of_pos`
- Dependency: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeFaceCounts](CrownOrderPolytopeFaceCounts.md)
