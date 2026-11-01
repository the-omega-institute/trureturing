# Original cyclic vertices and internal diagonals

## Abstract

Literal forced-ear fans and original conditioned polygon completions

**Definition 1.1 (Cyclic independence).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{Independent}\left(P\right) \iff (\forall i \in \operatorname{ZMod}\left(n\right),\; ((i \in P) \implies \neg (((i + 1) \in P)))))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonConditionedFan.Independent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Independence forbids consecutive centres in ZMod n, including across the cyclic seam.

**Definition 1.2 (Literal forced-ear fan).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall h \in \operatorname{ZMod}\left(n\right),\; \forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((e \in \operatorname{fan}\left(P, h\right)) \iff ((\exists i \in \operatorname{ZMod}\left(n\right),\; ((i \in P) \land (\operatorname{ear}\left(i\right) = e))) \lor (\exists j \in \operatorname{ZMod}\left(n\right),\; (\neg ((j \in P)) \land (\operatorname{IsDiagonal}\left(\operatorname{symPair}\left(h, j\right)\right) \land (\operatorname{symPair}\left(h, j\right) = e))))))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonConditionedFan.fan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fan is the union of every forced original ear and every original internal root spoke whose other endpoint is outside P. Both parts are finite sets: coincident forced ears and spokes occur once. Vertices retain their original labels.

**Theorem 1.3 (A complete actual triangulation and its ears).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall h \in \operatorname{ZMod}\left(n\right),\; ((6 \leq n) \implies (\operatorname{Independent}\left(P\right) \implies (\neg ((h \in P)) \implies (\operatorname{IsTriangulation}\left(\operatorname{fan}\left(P, h\right)\right) \land ((P \subseteq \operatorname{EarCenters}\left(\operatorname{fan}\left(P, h\right)\right)) \land (\operatorname{EarCenters}\left(\operatorname{fan}\left(P, h\right)\right) \subseteq (P \cup \operatorname{insert}\left((h - 1), \operatorname{insert}\left((h + 1), \emptyset\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonConditionedFan.fan_triangulation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n at least 6, an independent P and a root outside P give an actual triangulation of the full original polygon. No restriction excludes empty P or forces the root neighbours to survive outside P. Internalness and strict cyclic noncrossing hold for every member. For maximality, an omitted internal chord with a forced endpoint crosses that forced ear. Otherwise, in coordinates relative to the root, let its endpoints be a<b. A surviving centre a+1 supplies a crossing spoke. If a+1 is forced, independence makes a+2 survive; the sole exceptional gap b=a+2 is already the forced ear at a+1. The ear bounds follow from injectivity of original ears and the endpoints of root spokes.

**Theorem 1.4 (Two distinct original diagonals cross the root ear).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall h \in \operatorname{ZMod}\left(n\right),\; ((6 \leq n) \implies (((\operatorname{card}\left(P\right) + 4) < n) \implies (\exists e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((e \in \operatorname{fan}\left(P, h\right)) \land (\exists f \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((f \in \operatorname{fan}\left(P, h\right)) \land (\neg ((e = f)) \land (\operatorname{IsDiagonal}\left(e\right) \land (\operatorname{IsDiagonal}\left(f\right) \land (\operatorname{Cross}\left(e, \operatorname{ear}\left(h\right)\right) \land \operatorname{Cross}\left(f, \operatorname{ear}\left(h\right)\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonConditionedFan.fan_two_crossings` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This stronger statement needs only n at least 6 and |P|+4<n. The complement of P union {h,h-1,h+1} has more than one vertex. Two distinct targets give distinct symmetric-square spokes, each an original internal diagonal crossing ear(h). No count of all triangulation diagonals is used.

**Theorem 1.5 (Positive complete fibres and terminal empty traces).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((14 \leq n) \implies (\operatorname{Disjoint}\left(P, Q\right) \implies ((\forall i \in \operatorname{ZMod}\left(n\right),\; \forall j \in \operatorname{ZMod}\left(n\right),\; ((i \in (P \cup Q)) \implies ((j \in (P \cup Q)) \implies (\neg ((i = j)) \implies \neg (\operatorname{Cross}\left(\operatorname{ear}\left(i\right), \operatorname{ear}\left(j\right)\right)))))) \implies ((((\operatorname{card}\left(P\right) = 2) \land (\operatorname{card}\left(Q\right) = 2)) \lor (((\operatorname{card}\left(P\right) = 3) \land (\operatorname{card}\left(Q\right) = 3)) \lor (((\operatorname{card}\left(P\right) = 2) \land (\operatorname{card}\left(Q\right) = 4)) \lor ((\operatorname{card}\left(P\right) = 4) \land (\operatorname{card}\left(Q\right) = 2))))) \implies (\operatorname{Nonempty}\left(\operatorname{ConditionFiber}\left(P, Q, \emptyset, \emptyset\right)\right) \land ((0 < \operatorname{Natcard}\left(\operatorname{ConditionFiber}\left(P, Q, \emptyset, \emptyset\right)\right)) \land ((\exists h \in \operatorname{ZMod}\left(n\right),\; (\neg ((h \in P)) \land (\exists T \in \operatorname{ConditionFiber}\left(P, Q, \emptyset, \emptyset\right),\; (\operatorname{val}\left(T\right) = \operatorname{fan}\left(P, h\right))))) \land (\forall H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((H \subseteq \operatorname{EK}\left((P \cup Q)\right)) \implies ((\forall i \in \operatorname{ZMod}\left(n\right),\; \forall j \in \operatorname{ZMod}\left(n\right),\; ((i \in H) \implies ((j \in H) \implies (\neg ((i = j)) \implies \neg (\operatorname{Cross}\left(\operatorname{ear}\left(i\right), \operatorname{ear}\left(j\right)\right)))))) \implies (\forall h \in \operatorname{ZMod}\left(n\right),\; ((h \in H) \implies (\exists T \in \operatorname{ConditionFiber}\left(P, Q, H, \emptyset\right),\; ((\operatorname{val}\left(T\right) = \operatorname{fan}\left(P, h\right)) \land (\exists e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((e \in \operatorname{val}\left(T\right)) \land (\exists f \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((f \in \operatorname{val}\left(T\right)) \land (\neg ((e = f)) \land (\operatorname{IsDiagonal}\left(e\right) \land (\operatorname{IsDiagonal}\left(f\right) \land (\operatorname{Cross}\left(e, \operatorname{ear}\left(h\right)\right) \land \operatorname{Cross}\left(f, \operatorname{ear}\left(h\right)\right)))))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonConditionedFan.source_conditioned_witnesses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

P,Q are disjoint and their union consists of pairwise noncrossing original ears. All four cases (2,2),(3,3),(2,4),(4,2) are included. Independence of P is derived from these geometric conditions. To obtain an actual conditioned completion, choose h outside P union (Q-1) union (Q+1), a set of size at most |P|+2|Q|<n. The root may belong to Q. The literal fan forces P and avoids Q, giving a member of the full ConditionFiber P Q empty empty and positive Nat.card. For every terminal pairwise noncrossing H contained in EK(P union Q) and every h in H, that same fan at h avoids Q union H and has two distinct original internal diagonals crossing ear(h). Thus its exact H trace is empty. ConditionFiber retains every original actual triangulation satisfying its conditions. Exchanging P,Q supplies the opposite direction separately. These are the geometric existence inputs for B-37.2 and the fan paragraph following (37.10), also used in B-34.4. Neither a Catalan count, a flip-image theorem, nor a normalized strict comparison is asserted. EK denotes E_K, Natcard denotes Nat.card, and val is the underlying original chord set.

## References

- Truth anchor: `D5/S3/Geometry/Polygons/PolygonConditionedFan.Independent`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonConditionedFan.fan`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonConditionedFan.fan_triangulation`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonConditionedFan.fan_two_crossings`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonConditionedFan.source_conditioned_witnesses`
- Dependency: [D5/S3/Geometry/Polygons/PolygonEarSlide](PolygonEarSlide.md)
