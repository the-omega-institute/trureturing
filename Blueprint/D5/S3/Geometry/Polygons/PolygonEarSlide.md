# Actual polygon carrier and cyclic order

## Abstract

Actual polygon condition preserving ear slide

**Definition 1.1 (Actual maximal diagonal carrier).**

Lean statement: `D5/S3/Geometry/Polygons/PolygonEarSlide.IsTriangulation`

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlide.IsTriangulation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Vertices are ZMod n and chords are unordered pairs. Internal diagonals are segments that are not boundary sides. Cross records the two cyclic betweenness witnesses, and an actual triangulation is a maximal noncrossing finite set of internal diagonals.

**Theorem 1.2 (Cyclic translation of triangulations).**

Lean statement: `D5/S3/Geometry/Polygons/PolygonEarSlide.isTriangulation_map_add`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.isTriangulation_map_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding a fixed vertex offset to every chord preserves internal diagonals, crossing, noncrossing, and maximality. The proof pulls every candidate diagonal back by the inverse offset.

**Theorem 1.3 (Crossing transport away from the deleted centre).**

Lean statement: `D5/S3/Geometry/Polygons/PolygonEarSlide.cross_chordSwap_of_avoidTwo`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.cross_chordSwap_of_avoidTwo` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The vertex permutation exchanges 1 and 2. A chord whose endpoints avoid 2 remains in the cyclic coordinate order after this exchange, including the cyclic seam, so crossing is preserved in both directions.

**Theorem 1.4 (Ear-centre exclusion).**

Lean statement: `D5/S3/Geometry/Polygons/PolygonEarSlide.avoidTwo_of_mem_triangulation`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.avoidTwo_of_mem_triangulation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If t={1,3} belongs to an actual triangulation, every internal diagonal incident with 2 crosses t and is absent. The analogous statement for s={0,2} excludes the exchanged centre.

**Definition 1.5 (Concrete erase, swap, and insert map).**

Lean statement: `D5/S3/Geometry/Polygons/PolygonEarSlide.phi`

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlide.phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map phi erases t, applies the vertex exchange to every retained chord, and inserts s. The inverse psi erases s, applies the same exchange, and inserts t. The inserted chord is treated separately in the maximality proofs.

**Theorem 1.6 (Actual triangulation preservation).**

Lean statement: `D5/S3/Geometry/Polygons/PolygonEarSlide.phi_isTriangulation`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.phi_isTriangulation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every source triangulation containing t, phi is an actual triangulation. Diagonal and noncrossing preservation use the exclusion of centre 2; maximality pulls a target candidate back through the exchange and handles the fresh chord s separately. The corresponding statement holds for psi.

**Theorem 1.7 (Inverse laws on complete chord sets).**

Lean statement: `D5/S3/Geometry/Polygons/PolygonEarSlide.psi_phi`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.psi_phi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the actual diagonal membership and ear containment conditions, psi(phi T)=T and phi(psi U)=U. These are equalities of complete finite chord sets, so no selected completion or witness is introduced.

**Theorem 1.8 (Exact observed-ear trace transport).**

Lean statement: `D5/S3/Geometry/Polygons/PolygonEarSlide.trace_phi`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.trace_phi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every ear centre outside 0,1,2,3 is fixed by the vertex exchange. The source trace containing centre 2 therefore becomes the target trace containing centre 1 after erasing centres 2 and 3 from the observed set; centre 3 is free on the target side. The inverse trace statement is proved independently.

**Theorem 1.9 (Normalized condition fibre equivalence).**

Lean statement: `D5/S3/Geometry/Polygons/PolygonEarSlide.condition_fibre_equiv`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.condition_fibre_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least 14, disjoint compatible forced and forbidden ear sets P and Q of cardinalities (2,2), (3,3), (2,4), or (4,2), and an observed set J inside the compatible carrier E_K, the subtype of all actual triangulations with trace insert 2 R is equivalent to the subtype with trace insert 1 R on J.erase 2.erase 3. Empty subtypes are included. The P, Q, and R coordinates are discharged from the carrier hypotheses.

**Theorem 1.10 (Arbitrary cyclic block placement).**

Lean statement: `D5/S3/Geometry/Polygons/PolygonEarSlide.condition_fibre_equiv_at`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.condition_fibre_equiv_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any cyclic start a, conjugating the normalized equivalence by verified translation gives the full fibre equivalence with source trace insert (a+2) R and target trace insert (a+1) R on J.erase (a+2).erase (a+3). All actual triangulation completions and infeasible fibres remain in the two subtype fibres.

## References

- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.IsTriangulation`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.avoidTwo_of_mem_triangulation`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.condition_fibre_equiv`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.condition_fibre_equiv_at`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.cross_chordSwap_of_avoidTwo`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.isTriangulation_map_add`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.phi`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.phi_isTriangulation`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.psi_phi`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.trace_phi`
