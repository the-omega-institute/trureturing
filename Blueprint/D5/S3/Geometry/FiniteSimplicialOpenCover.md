# Positive coordinate stars of a finite complex

## Abstract

Positive coordinate stars of a finite complex.

**Definition 1.1 (Open vertex stars).**

Lean statement: `D5/S3/Geometry/FiniteSimplicialOpenCover.vertexOpen`

*Formalization.* `D5/S3/Geometry/FiniteSimplicialOpenCover.vertexOpen` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite linearly ordered vertex type V and pre-abstract simplicial complex K, the carrier is the subtype of real coordinate vectors in FiniteConeCollapse.realization K. The star of v consists exactly of points with strictly positive v coordinate. Ghost vertices give empty stars.

**Theorem 1.2 (A cover of the actual carrier).**

Lean statement: `D5/S3/Geometry/FiniteSimplicialOpenCover.vertexOpen_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplicialOpenCover.vertexOpen_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The vertex stars are open in the coordinate subspace topology and cover the entire carrier. The existing FiniteConeCollapse.realization_mem_iff identifies a realized point with a point in an actual face simplex, giving nonnegative coordinates summing to one, so some coordinate is positive. The carrier may be empty.

**Theorem 1.3 (Intersections detect faces).**

Lean statement: `D5/S3/Geometry/FiniteSimplicialOpenCover.face_of_nonempty_intersection`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplicialOpenCover.face_of_nonempty_intersection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a nonempty finite vertex set has a point in its positive-coordinate intersection, it is a face of K. Positivity places all selected vertices in a support face of that same point; downward closure then applies.

**Definition 1.4 (Straight-line contraction).**

Lean statement: `D5/S3/Geometry/FiniteSimplicialOpenCover.intersectionContraction`

*Formalization.* `D5/S3/Geometry/FiniteSimplicialOpenCover.intersectionContraction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any actual face s, the equal-weight barycenter lies in its intersection. The straight segment from each intersection point to that barycenter stays in the original support face and retains positivity on s. This gives a continuous homotopy from the identity to the constant barycenter map.

**Theorem 1.5 (Contractible face intersections).**

Lean statement: `D5/S3/Geometry/FiniteSimplicialOpenCover.contractible_intersection`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplicialOpenCover.contractible_intersection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual face has a contractible positive-coordinate intersection, with the displayed barycenter and homotopy. The empty intersection is the whole carrier and is not asserted to be contractible.

## References

- Truth anchor: `D5/S3/Geometry/FiniteSimplicialOpenCover.contractible_intersection`
- Truth anchor: `D5/S3/Geometry/FiniteSimplicialOpenCover.face_of_nonempty_intersection`
- Truth anchor: `D5/S3/Geometry/FiniteSimplicialOpenCover.intersectionContraction`
- Truth anchor: `D5/S3/Geometry/FiniteSimplicialOpenCover.vertexOpen`
- Truth anchor: `D5/S3/Geometry/FiniteSimplicialOpenCover.vertexOpen_cover`
- Dependency: [D5/S3/Geometry/FiniteConeCollapse](FiniteConeCollapse.md)
