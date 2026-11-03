# The filled polygon convention

## Abstract

Filled convex polygons and their genuine corners

Let E be a real normed plane and p an actual Polygon E n, with its native Fin(n) cyclic successor. Write hull(p) for the real convex hull of range(p.vertices). FilledModel(p,C) states that C is compact and convex with nonempty ordinary interior, p.vertices is injective, p.boundary over the reals equals frontier(C), and every three consecutive vertices are affinely independent. These are genuine noncollinear corners. The boundary is the union of the actual closed successor segments. No extremality, diagonal interiority, cyclic alternation or crossing condition occurs in this definition.

The ordinary filled strictly convex polygon convention means a compact convex filled region with nonempty interior, traversed once by its distinct genuine corners in cyclic boundary order. Flat sides are allowed: strict convexity is required of the corners, not of the filled set. Such a traversal supplies the boundary equality and injectivity in FilledModel. The theorem only needs these consequences of the traversal. It does not assert the separate classical equivalence from a merely simple polygon with no reflex angles to this filled convention.

**Theorem 1.1 (The filled region and the extreme-vertex model).**

$$\forall E \in Type,\; [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(Real, E\right)], \forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], ((\operatorname{finrank}\left(Real, E\right) = 2) \implies \forall p \in \operatorname{Polygon}\left(E, n\right),\; \forall C \in \operatorname{Set}\left(E\right),\; (\operatorname{FilledModel}\left(p, C\right) \implies ((C = \operatorname{hull}\left(p\right)) \land \operatorname{BoundaryModel}\left(p\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonFilledBoundary.boundaryModel_of_filled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

First, every vertex belongs to C through its incident boundary segment, so hull(p) is contained in C. If a point of C were outside this finite closed hull, strict separation would supply a nonzero continuous linear functional larger there than everywhere on the hull. Its maximum on compact C cannot be interior: the image of an open neighborhood under a nonzero functional is open and cannot stay below its maximum. Thus the maximizer lies on frontier(C), hence on an actual successor edge and therefore in the hull. This contradicts strict separation and proves C=hull(p).

For each actual edge, support at its midpoint supplies a nonzero continuous functional. Since that midpoint is a strict convex combination of the edge endpoints, both endpoints attain the support maximum. In a real plane the common level of a nonzero functional through two distinct points is their affine line: a third noncollinear point on the level would span the plane and force the functional to be constant and zero.

At a genuine corner, use the supporting functionals of its incoming and outgoing edges. If the corner lies strictly between two points of C, both points attain both support maxima. They lie on both incident lines. Noncollinearity of the three consecutive corners makes their common point exactly the corner. This proves extremality. Hull equality then turns the original boundary equality into BoundaryModel for the same polygon, without replacing its vertices or cyclic indexing.

For an original fixed labelled fourteen-gon under the stated filled convention, use this theorem with n=14 and the original C and p. Its second conclusion feeds PolygonInteriorDiagonals.isDiagonal_iff_openSegment_subset_interior directly. Under the canonical ZMod.finEquiv relabelling, every original nonloop nonside vertex pair has its whole open chord in interior(C), and conversely; both side orientations, the seam, loops and every non-ear diagonal stay in scope. This is an application of the existing G4 result, with no new named specialization.

For the same filled fourteen-gon, feed the resulting BoundaryModel into PolygonCyclicCrossing.cross_iff_properCross and then apply PolygonCompressionTrace.cross_ear_iff_adjacent to the original ears pair(i-1,i+1). This derives proper geometric crossing exactly when the original centres are cyclic neighbors, the literal first sentence of the existing section 40.2. The direct application keeps the same polygon, region and cyclic labels. Whole geometric triangulations and maximality, complete-ear and arbitrary-family transports, witnesses, completion fibres and counts are separate obligations.

## References

- Truth anchor: `D5/S3/Geometry/Polygons/PolygonFilledBoundary.boundaryModel_of_filled`
- Dependency: [D5/S3/Geometry/Polygons/PolygonInteriorDiagonals](PolygonInteriorDiagonals.md)
