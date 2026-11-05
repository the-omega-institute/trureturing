# Actual carrier and cyclic crossing geometry

## Abstract

Actual polygon ear slide geometry

**Definition 1.1 (Segments).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{IsSegment}\left(e\right) \iff \neg (\operatorname{IsDiag}\left(e\right)))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlideGeometry.IsSegment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A segment has distinct endpoints in the symmetric square.

**Definition 1.2 (Boundary sides).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{IsSide}\left(e\right) \iff (\exists i \in \operatorname{ZMod}\left(n\right),\; (e = \operatorname{symPair}\left(i, (i + 1)\right))))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlideGeometry.IsSide` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An unordered boundary side joins successive cyclic vertices. symPair denotes the unordered pair s(a,b).

**Definition 1.3 (Internal diagonals).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{IsDiagonal}\left(e\right) \iff (\operatorname{IsSegment}\left(e\right) \land \neg (\operatorname{IsSide}\left(e\right))))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlideGeometry.IsDiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Internal diagonals are segments that are not boundary sides.

**Definition 1.4 (Actual cyclic crossing).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall f \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{Cross}\left(e, f\right) \iff (\exists a \in \operatorname{ZMod}\left(n\right),\; \exists b \in \operatorname{ZMod}\left(n\right),\; \exists c \in \operatorname{ZMod}\left(n\right),\; \exists d \in \operatorname{ZMod}\left(n\right),\; ((e = \operatorname{symPair}\left(a, b\right)) \land ((f = \operatorname{symPair}\left(c, d\right)) \land (\operatorname{sbtw}\left(a, c, b\right) \land \operatorname{sbtw}\left(b, d, a\right))))))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlideGeometry.Cross` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Crossing uses strict cyclic betweenness witnesses.

**Definition 1.5 (Maximal noncrossing finite diagonal carrier).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; (\operatorname{IsTriangulation}\left(T\right) \iff ((\forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((e \in T) \implies \operatorname{IsDiagonal}\left(e\right))) \land ((\forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall f \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((e \in T) \implies ((f \in T) \implies \neg (\operatorname{Cross}\left(e, f\right))))) \land (\forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{IsDiagonal}\left(e\right) \implies (\neg ((e \in T)) \implies (\exists f \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((f \in T) \land \operatorname{Cross}\left(e, f\right)))))))))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlideGeometry.IsTriangulation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier contains every maximal noncrossing finite set of internal diagonals; no completion is selected.

**Definition 1.6 (Ear diagonal at a cyclic centre).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall i \in \operatorname{ZMod}\left(n\right),\; (\operatorname{ear}\left(i\right) = \operatorname{symPair}\left((i - 1), (i + 1)\right))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlideGeometry.ear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The local names sEar, tEar, uEar denote ear(1), ear(2), ear(3).

**Definition 1.7 (Exchange the two local vertices).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall i \in \operatorname{ZMod}\left(n\right),\; (\operatorname{vertexSwap}\left(n, i\right) = \operatorname{swap}\left(1, 2, i\right))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlideGeometry.vertexSwap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vertex permutation exchanges 1 and 2 and fixes every other vertex.

**Definition 1.8 (Induced unordered-chord exchange).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{chordSwap}\left(e\right) = \operatorname{map}\left(\operatorname{vertexSwap}\left(n\right), e\right))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlideGeometry.chordSwap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Symmetric-square map transports each unordered pair.

**Definition 1.9 (Avoid the deleted centre).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{AvoidTwo}\left(e\right) \iff (\forall x \in \operatorname{ZMod}\left(n\right),\; \neg ((e = \operatorname{symPair}\left(2, x\right)))))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlideGeometry.AvoidTwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every endpoint avoids vertex 2.

**Theorem 1.10 (Crossing transport away from centre 2).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall f \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((6 \leq n) \implies (\operatorname{AvoidTwo}\left(e\right) \implies (\operatorname{AvoidTwo}\left(f\right) \implies (\operatorname{Cross}\left(\operatorname{chordSwap}\left(e\right), \operatorname{chordSwap}\left(f\right)\right) \iff \operatorname{Cross}\left(e, f\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlideGeometry.cross_chordSwap_of_avoidTwo` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Crossing is transported in both directions, including across the cyclic seam.

## References

- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlideGeometry.AvoidTwo`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlideGeometry.Cross`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlideGeometry.IsDiagonal`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlideGeometry.IsSegment`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlideGeometry.IsSide`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlideGeometry.IsTriangulation`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlideGeometry.chordSwap`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlideGeometry.cross_chordSwap_of_avoidTwo`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlideGeometry.ear`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlideGeometry.vertexSwap`
