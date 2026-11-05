# Extreme vertices and the filled hull

## Abstract

Interior diagonals from an actual polygon boundary

Let E be a real normed vector space of real dimension two and let p be a Polygon E n with n at least three. Put hull(p)=convexHull over the reals of the range of p.vertices. BoundaryModel(p) states precisely that the vertices are injective, every vertex is an extreme point of hull(p), and p.boundary over the reals equals the topological frontier of hull(p). The native boundary is the union of p.edgeSet over Fin(n); each edge joins p(k) to p(finRotate n k). The vertex map on ZMod(n) is p composed with the inverse of ZMod.finEquiv n. The notation pair(i,j) denotes the unordered pair s(i,j). IsDiagonal is the existing native predicate: distinct endpoints and absence from the cyclic successor sides.

**Theorem 1.1 (Every native diagonal and only those diagonals).**

$$\forall E \in Type,\; [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(Real, E\right)], \forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], ((\operatorname{finrank}\left(Real, E\right) = 2) \implies ((3 \leq n) \implies \forall p \in \operatorname{Polygon}\left(E, n\right),\; (\operatorname{BoundaryModel}\left(p\right) \implies \forall i \in \operatorname{ZMod}\left(n\right),\; \forall j \in \operatorname{ZMod}\left(n\right),\; (\operatorname{IsDiagonal}\left(\operatorname{pair}\left(i, j\right)\right) \iff ((\operatorname{vertex}\left(p, i\right) \neq \operatorname{vertex}\left(p, j\right)) \land (\operatorname{openSegment}\left(Real, \operatorname{vertex}\left(p, i\right), \operatorname{vertex}\left(p, j\right)\right) \subseteq \operatorname{interior}\left(\operatorname{hull}\left(p\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonInteriorDiagonals.isDiagonal_iff_openSegment_subset_interior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Three distinct extreme vertices cannot be collinear: one would lie between the other two and extremality would make it an endpoint. Such a triple spans the plane, so the finite convex hull has nonempty interior. The affine-span and interior implications use the corresponding Mathlib results directly.

Suppose two distinct listed vertices maximize one nonzero continuous linear functional. Their midpoint belongs to the hull and cannot be interior: a nonzero functional maps open sets to open sets, whereas the hull stays below its maximum. Boundary coverage puts that midpoint on an actual cyclic edge. It cannot be an edge endpoint by extremality. Both edge endpoints therefore attain the same maximum. Three distinct listed vertices on this level would span the plane and force the functional to be constant and hence zero. The two endpoint pairs coincide, proving actual successor adjacency.

Now take any point of the open chord of a native diagonal. Convexity puts it in the hull. If it were not interior, the nonempty-interior supporting-functional theorem would supply a nonzero functional maximizing there; both chord endpoints would maximize it. The preceding adjacency conclusion contradicts the diagonal predicate. Conversely, a cyclic side lies on the frontier and its midpoint cannot lie in the interior. The explicit distinctness conjunct excludes loops, including the convention that an open segment from a point to itself contains that point. Both successor orientations and the cyclic seam are included.

This result assumes the explicit extreme-vertex boundary model. It requires no strict convexity of the filled set, regularity, metric angle data, alternation condition or orientation theorem. It does not identify a simple polygon with no reflex angles with this model, establish the alternating-arc or proper-crossing characterization, or transport whole triangulations, maximality, complete ears, families, witnesses or completion counts. Those geometric correspondences require further theorems.

## References

- Truth anchor: `D5/S3/Geometry/Polygons/PolygonInteriorDiagonals.isDiagonal_iff_openSegment_subset_interior`
- Dependency: [D5/S3/Geometry/Polygons/PolygonEarSlideGeometry](PolygonEarSlideGeometry.md)
