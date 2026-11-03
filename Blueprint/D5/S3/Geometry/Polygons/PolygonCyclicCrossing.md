# The same polygon and all labelled chords

## Abstract

Cyclic arcs and proper crossing of actual polygon chords

Let p be an actual real normed plane polygon satisfying BoundaryModel, with n at least three. Use precisely its existing ZMod.finEquiv relabelling and successor edges. Pair(a,b) is the native unordered pair, and Cross is its existing cyclic alternation predicate. ProperCross(p,e,f) instead requires representatives of e and f whose actual endpoints are distinct within each chord, whose two endpoint sets are disjoint, and whose actual open segments have a common point. It contains no cyclic-order or native-Cross condition. Thus loops, shared endpoints and coincident chords are explicitly excluded even though Mathlib's open segment from a point to itself is nonempty.

**Theorem 1.1 (Strict side constancy on each actual cyclic open arc).**

$$\forall E \in Type,\; [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(Real, E\right)], \forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], ((\operatorname{finrank}\left(Real, E\right) = 2) \implies ((3 \leq n) \implies \forall p \in \operatorname{Polygon}\left(E, n\right),\; (\operatorname{BoundaryModel}\left(p\right) \implies \forall a \in \operatorname{ZMod}\left(n\right),\; \forall b \in \operatorname{ZMod}\left(n\right),\; \forall c \in \operatorname{ZMod}\left(n\right),\; \forall d \in \operatorname{ZMod}\left(n\right),\; ((a \neq b) \implies (\operatorname{sbtw}\left(a, c, b\right) \implies (\operatorname{sbtw}\left(a, d, b\right) \implies \forall f \in \operatorname{ContinuousLinearMap}\left(Real, E, Real\right),\; ((f \neq 0) \implies ((\operatorname{f}\left(\operatorname{vertex}\left(p, b\right)\right) = \operatorname{f}\left(\operatorname{vertex}\left(p, a\right)\right)) \implies (((\operatorname{f}\left(\operatorname{vertex}\left(p, c\right)\right) - \operatorname{f}\left(\operatorname{vertex}\left(p, a\right)\right)) \times (\operatorname{f}\left(\operatorname{vertex}\left(p, d\right)\right) - \operatorname{f}\left(\operatorname{vertex}\left(p, a\right)\right))) > 0)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCyclicCrossing.same_arc_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose any nonzero continuous linear functional with equal values at the distinct chord endpoints. No third extreme vertex can have that value in a plane. If the functional changed sign across an actual successor edge away from the chord endpoints, its zero level would meet that edge in an open-segment point. The chord line intersects the hull only in the chord segment by endpoint extremality. G4 makes every open diagonal point interior, contradicting boundary coverage; the supporting-functional argument handles the side case using the existing G4 maximal-endpoint and common-level results.

Write L=(b-a).val and w(k)=a+k. The existing basePos circular-order supplier identifies sbtw(a,x,b) exactly with 0<(x-a).val<L. Finite induction over successive k propagates the strict sign along this actual chain. This includes wraparound without changing the polygon or replacing the cyclic order. An adjacent chord has an empty short open arc, so no strict-side assertion is imposed on that absent chain.

**Theorem 1.2 (Actual opposite sides and cyclic alternation).**

$$\forall E \in Type,\; [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(Real, E\right)], \forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], ((\operatorname{finrank}\left(Real, E\right) = 2) \implies ((3 \leq n) \implies \forall p \in \operatorname{Polygon}\left(E, n\right),\; (\operatorname{BoundaryModel}\left(p\right) \implies \forall a \in \operatorname{ZMod}\left(n\right),\; \forall b \in \operatorname{ZMod}\left(n\right),\; \forall c \in \operatorname{ZMod}\left(n\right),\; \forall d \in \operatorname{ZMod}\left(n\right),\; ((a \neq b) \implies ((c \neq a) \implies ((c \neq b) \implies ((d \neq a) \implies ((d \neq b) \implies (\operatorname{SOppSide}\left(\operatorname{line}\left(Real, \operatorname{vertex}\left(p, a\right), \operatorname{vertex}\left(p, b\right)\right), \operatorname{vertex}\left(p, c\right), \operatorname{vertex}\left(p, d\right)\right) \iff \operatorname{Cross}\left(\operatorname{pair}\left(a, b\right), \operatorname{pair}\left(c, d\right)\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCyclicCrossing.sOppSide_iff_cross` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two nonempty open arcs had the same strict sign, constancy and the exact two-arc partition would put all vertices in the same closed functional halfplane. Convex-hull minimality extends this bound to the hull. The existing supporting_pair_is_side theorem forces the chord endpoints to be cyclic successors, contrary to nonemptiness of the short arc. The two arcs therefore have opposite signs.

The one-dimensional span of the chord difference is proper in the plane. Apply Mathlib's nonzero annihilator theorem and finite-dimensional continuity to obtain the required chord functional. Its level is exactly the chord line. Strict opposite scalar signs are equivalent to SOppSide: scalar interpolation produces an actual open-segment point on the line, and conversely the SOppSide betweenness witness maps into the scalar interval. Combining this equivalence with the two actual arc signs gives precisely native Cross. The conclusion allows c=d, for which both sides are false; four distinct labels are included.

**Theorem 1.3 (The complete native chord universe).**

$$\forall E \in Type,\; [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(Real, E\right)], \forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], ((\operatorname{finrank}\left(Real, E\right) = 2) \implies ((3 \leq n) \implies \forall p \in \operatorname{Polygon}\left(E, n\right),\; (\operatorname{BoundaryModel}\left(p\right) \implies \forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall f \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{Cross}\left(e, f\right) \iff \operatorname{ProperCross}\left(p, e, f\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCyclicCrossing.cross_iff_properCross` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For alternating labels, SOppSide gives an actual intersection point of the second open chord with the first chord line. Hull convexity and extremality of the first endpoints put that point in the first open chord. Conversely, a proper open-chord intersection gives strict betweenness through the first line. No third extreme vertex lies on this line, so the second endpoints are strictly on opposite sides and the preceding theorem gives native Cross. The theorem quantifies over every unordered vertex pair, with no ear-only or nondegeneracy restriction on the input universe. Loops, either side orientation, the seam, shared endpoints, coincident chords and non-ear diagonals are all covered.

Under the ordinary filled-convex genuine-corners convention for the fixed labelled fourteen-gon in the original source, PolygonFilledBoundary.boundaryModel_of_filled supplies BoundaryModel for the very same p and C. Apply this crossing theorem to the original ears e_i=pair(i-1,i+1), and apply PolygonCompressionTrace.cross_ear_iff_adjacent with n=14. It follows that these actual original ear chords properly geometrically cross exactly when j=i+1 or i=j+1 modulo fourteen. This is the literal first sentence of the existing section 40.2. It is a direct application, with no retained ear specialization or new theory clause.

This correspondence does not establish the equivalence from a merely simple no-reflex predicate, whole geometric triangulations or maximality, complete-ear transports, arbitrary-family transports, witness conditions, completion fibres or counting. The remaining clauses of the mixed source atom and the broader original C0 and FIB objectives remain separate obligations.

## References

- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCyclicCrossing.cross_iff_properCross`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCyclicCrossing.sOppSide_iff_cross`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCyclicCrossing.same_arc_sign`
- Dependency: [D5/S3/Geometry/Polygons/PolygonCatalanSupplier](PolygonCatalanSupplier.md)
- Dependency: [D5/S3/Geometry/Polygons/PolygonFilledBoundary](PolygonFilledBoundary.md)
