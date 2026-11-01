# Mutually inverse maps on actual triangulations

## Abstract

Complete polygon ear slide maps

**Theorem 1.1 (Ear-centre exclusion).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; \forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((6 \leq n) \implies (\operatorname{IsTriangulation}\left(T\right) \implies ((\operatorname{ear}\left(2\right) \in T) \implies ((e \in T) \implies \operatorname{AvoidTwo}\left(e\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlideMaps.avoidTwo_of_mem_triangulation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A triangulation containing t has no internal diagonal incident with its centre 2.

**Definition 1.2 (Forward complete chord map).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; (\operatorname{phi}\left(T\right) = \operatorname{insert}\left(\operatorname{ear}\left(1\right), \operatorname{image}\left(chordSwap, \operatorname{erase}\left(T, \operatorname{ear}\left(2\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlideMaps.phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Erase t, exchange vertices 1 and 2 in every retained chord, and insert s.

**Definition 1.3 (Inverse complete chord map).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; (\operatorname{psi}\left(T\right) = \operatorname{insert}\left(\operatorname{ear}\left(2\right), \operatorname{image}\left(chordSwap, \operatorname{erase}\left(T, \operatorname{ear}\left(1\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlideMaps.psi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Erase s, apply the same vertex exchange, and insert t.

**Theorem 1.4 (Forward actual triangulation preservation).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; ((6 \leq n) \implies (\operatorname{IsTriangulation}\left(T\right) \implies ((\operatorname{ear}\left(2\right) \in T) \implies \operatorname{IsTriangulation}\left(\operatorname{phi}\left(T\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlideMaps.phi_isTriangulation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Diagonal and crossing preservation use ear-centre exclusion; maximality handles the fresh s separately.

**Theorem 1.5 (Inverse actual triangulation preservation).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; ((6 \leq n) \implies (\operatorname{IsTriangulation}\left(T\right) \implies ((\operatorname{ear}\left(1\right) \in T) \implies \operatorname{IsTriangulation}\left(\operatorname{psi}\left(T\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlideMaps.psi_isTriangulation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse preserves the full maximal diagonal carrier.

**Theorem 1.6 (Left inverse on complete chord sets).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; ((6 \leq n) \implies ((\forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((e \in T) \implies \operatorname{IsDiagonal}\left(e\right))) \implies ((\operatorname{ear}\left(2\right) \in T) \implies (\neg ((\operatorname{ear}\left(1\right) \in T)) \implies (\operatorname{psi}\left(\operatorname{phi}\left(T\right)\right) = T)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlideMaps.psi_phi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse law requires only diagonal membership and the stated included and excluded ears.

**Theorem 1.7 (Right inverse on complete chord sets).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; ((6 \leq n) \implies ((\forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((e \in T) \implies \operatorname{IsDiagonal}\left(e\right))) \implies ((\operatorname{ear}\left(1\right) \in T) \implies (\neg ((\operatorname{ear}\left(2\right) \in T)) \implies (\operatorname{phi}\left(\operatorname{psi}\left(T\right)\right) = T)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlideMaps.phi_psi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality holds for the entire finite chord set.

## References

- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlideMaps.avoidTwo_of_mem_triangulation`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlideMaps.phi`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlideMaps.phi_isTriangulation`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlideMaps.phi_psi`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlideMaps.psi`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlideMaps.psi_isTriangulation`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlideMaps.psi_phi`
- Dependency: [D5/S3/Geometry/Polygons/PolygonEarSlideGeometry](PolygonEarSlideGeometry.md)
