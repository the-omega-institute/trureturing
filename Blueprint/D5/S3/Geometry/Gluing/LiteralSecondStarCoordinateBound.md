# A literal second-subdivision star inherits the 25/48 bound

## Abstract

The sharp coordinate bound for a literal standard second star

The standard vertices are the four coordinate unit vectors in the real function space on Fin(4). The literal second closed star is defined from the actual chains of faces and their barycenters. The main theorem transports a point of that literal star to a parent flag, expands its parent convex combination into barycentric face weights, and applies the sharp parent-star estimate.

**Definition 1.1 (The four standard coordinate vertices).**

Lean statement: `D5/S3/Geometry/Gluing/LiteralSecondStarCoordinateBound.standardVertices`

*Formalization.* `D5/S3/Geometry/Gluing/LiteralSecondStarCoordinateBound.standardVertices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

standardVertices assigns to each element of Fin(4) the corresponding coordinate unit vector in the real function space on Fin(4).

**Theorem 1.2 (The standard coordinate vertices are affinely independent).**

Lean statement: `D5/S3/Geometry/Gluing/LiteralSecondStarCoordinateBound.standardVertices_affineIndependent`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/LiteralSecondStarCoordinateBound.standardVertices_affineIndependent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four unit vectors have unique affine coefficients: equality of two affine combinations can be read one coordinate at a time.

**Theorem 1.3 (Every coordinate of a literal standard closed star is at least 25/48).**

Lean statement: `D5/S3/Geometry/Gluing/LiteralSecondStarCoordinateBound.literal_standard_closed_star_coordinate_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/LiteralSecondStarCoordinateBound.literal_standard_closed_star_coordinate_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If x belongs to the literal second closed star at the standard vertex i, then its i-th coordinate is at least 25/48.

The literal-to-parent-star correspondence supplies a permutation whose first flag entry is i. A convex-hull representation of x is expanded into coefficients on the four parent flag vertices. The parent-star characterization makes the zeroth coefficient maximal, and the parent linear estimate then gives the stated lower bound. The first coordinate of the parent flag vertex of rank k is exactly 1/(k+1), so the resulting weighted expression is the i-th coordinate of x.

## References

- Truth anchor: `D5/S3/Geometry/Gluing/LiteralSecondStarCoordinateBound.literal_standard_closed_star_coordinate_bound`
- Truth anchor: `D5/S3/Geometry/Gluing/LiteralSecondStarCoordinateBound.standardVertices`
- Truth anchor: `D5/S3/Geometry/Gluing/LiteralSecondStarCoordinateBound.standardVertices_affineIndependent`
- Dependency: [D5/S3/Geometry/Gluing/LiteralBarycentricSubdivisionStar](LiteralBarycentricSubdivisionStar.md)
- Dependency: [D5/S3/Geometry/Gluing/SecondBarycentricCoordinateBound](SecondBarycentricCoordinateBound.md)
