# Whole triangulation carriers

## Abstract

Deletion and insertion of actual polygon ears

V(k)=ZMod(k), C(k)=Sym2(V(k)), F(k)=Finset(C(k)). A(k) is the subtype of every U in F(k) satisfying Carrier.IsTriangulation U: internal-diagonal validity, pairwise noncrossing, and a crossing member for every missing internal diagonal. B(k,i) is the subtype of every T in F(k) satisfying IsTriangulation T and ear(i) in T. H(k,P) is the subtype of every T in F(k) satisfying IsTriangulation T and P subset EarCenters(T). Equiv means an actual bijection of these full subtypes. ne denotes inequality, notCross negates Carrier.Cross, and natSub is natural subtraction. Symtwo denotes Sym2. hasType(e,Equiv(A,B)) means e is the displayed equivalence from A to B; app, symm and val give application, inverse and the underlying full chord set. sub denotes subtraction in the cyclic vertex group. image(S,f) is the image of S under f, and map(e,f) maps both endpoints. choice is Classical.choice, and forcedequivexists denotes the private constructed Nonempty equivalence proof forced_equiv_exists. All natural casts in the vertex maps have the displayed modulus.

**Definition 1.1 (Insert vertex 1).**

$$\forall m \in Nat,\; \forall x \in \operatorname{ZMod}\left(m\right),\; (\operatorname{vertexLift}\left(x\right) = \operatorname{natCast}\left(\operatorname{ite}\left((\operatorname{val}\left(x\right) = 0), 0, (\operatorname{val}\left(x\right) + 1)\right), (m + 1)\right))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarContraction.vertexLift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural representative zero stays zero; each positive representative increases by one. The cast lands in ZMod(m+1).

**Definition 1.2 (Relabel after deletion).**

$$\forall m \in Nat,\; \forall x \in \operatorname{ZMod}\left((m + 1)\right),\; (\operatorname{vertexDrop}\left(x\right) = \operatorname{natCast}\left(\operatorname{natSub}\left(\operatorname{val}\left(x\right), 1\right), m\right))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarContraction.vertexDrop` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Drop uses natural subtraction and casting into ZMod(m). Its value at the deleted vertex is never used on a retained chord.

**Definition 1.3 (Map both endpoints).**

$$\forall m \in Nat,\; \forall e \in \operatorname{Symtwo}\left(\operatorname{ZMod}\left(m\right)\right),\; (\operatorname{chordLift}\left(e\right) = \operatorname{map}\left(e, \operatorname{vertexLift}\left(\right)\right))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarContraction.chordLift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unordered chord is mapped endpoint by endpoint.

**Definition 1.4 (Map both endpoints).**

$$\forall m \in Nat,\; \forall e \in \operatorname{Symtwo}\left(\operatorname{ZMod}\left((m + 1)\right)\right),\; (\operatorname{chordDrop}\left(e\right) = \operatorname{map}\left(e, \operatorname{vertexDrop}\left(\right)\right))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarContraction.chordDrop` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unordered chord is mapped endpoint by endpoint.

**Theorem 1.5 (Exact boundary correspondence).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], \forall e \in \operatorname{Symtwo}\left(\operatorname{ZMod}\left(m\right)\right),\; ((5 \leq m) \implies (\operatorname{IsSide}\left(e\right) \iff (\operatorname{IsSide}\left(\operatorname{chordLift}\left(e\right)\right) \lor (\operatorname{chordLift}\left(e\right) = \operatorname{ear}\left(1\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarContraction.boundary_lift_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reduced boundary lifts precisely to original boundary sides with surviving endpoints together with the forced ear. The two original sides incident to the removed centre are absent.

**Definition 1.6 (Delete the forced ear).**

$$\forall m \in Nat,\; \forall T \in \operatorname{Finset}\left(\operatorname{Symtwo}\left(\operatorname{ZMod}\left((m + 1)\right)\right)\right),\; (\operatorname{reduce}\left(T\right) = \operatorname{image}\left(\operatorname{erase}\left(T, \operatorname{ear}\left(1\right)\right), \operatorname{chordDrop}\left(\right)\right))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarContraction.reduce` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Erase ear(1), keep every other original chord, and relabel its surviving endpoints.

**Definition 1.7 (Insert the ear triangle).**

$$\forall m \in Nat,\; \forall U \in \operatorname{Finset}\left(\operatorname{Symtwo}\left(\operatorname{ZMod}\left(m\right)\right)\right),\; (\operatorname{expand}\left(U\right) = \operatorname{insert}\left(\operatorname{ear}\left(1\right), \operatorname{image}\left(U, \operatorname{chordLift}\left(\right)\right)\right))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarContraction.expand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lift every reduced chord and add exactly the forced ear.

**Theorem 1.8 (Deletion preserves full maximality).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Symtwo}\left(\operatorname{ZMod}\left((m + 1)\right)\right)\right),\; ((5 \leq m) \implies (\operatorname{IsTriangulation}\left(T\right) \implies ((\operatorname{ear}\left(1\right) \in T) \implies \operatorname{IsTriangulation}\left(\operatorname{reduce}\left(T\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarContraction.reduce_isTriangulation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A diagonal incident to centre 1 crosses the forced ear, so every retained chord avoids that centre. Strict cyclic order preserves crossing. For a missing reduced diagonal, original maximality supplies a crossing chord distinct from the ear, which therefore survives deletion.

**Theorem 1.9 (Insertion preserves full maximality).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], \forall U \in \operatorname{Finset}\left(\operatorname{Symtwo}\left(\operatorname{ZMod}\left(m\right)\right)\right),\; ((5 \leq m) \implies (\operatorname{IsTriangulation}\left(U\right) \implies \operatorname{IsTriangulation}\left(\operatorname{expand}\left(U\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarContraction.expand_isTriangulation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A missing original internal diagonal either crosses the ear or avoids its centre and descends to a reduced internal diagonal. Reduced maximality then supplies an actual crossing chord. Boundary classification handles the new reduced boundary exactly.

**Theorem 1.10 (Recover every original chord).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Symtwo}\left(\operatorname{ZMod}\left((m + 1)\right)\right)\right),\; ((5 \leq m) \implies (\operatorname{IsTriangulation}\left(T\right) \implies ((\operatorname{ear}\left(1\right) \in T) \implies (\operatorname{expand}\left(\operatorname{reduce}\left(T\right)\right) = T))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarContraction.expand_reduce` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse recovers the entire original finite chord set, including the forced ear.

**Theorem 1.11 (Recover every reduced chord).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], \forall U \in \operatorname{Finset}\left(\operatorname{Symtwo}\left(\operatorname{ZMod}\left(m\right)\right)\right),\; ((5 \leq m) \implies (\operatorname{IsTriangulation}\left(U\right) \implies (\operatorname{reduce}\left(\operatorname{expand}\left(U\right)\right) = U)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarContraction.reduce_expand` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every internal reduced diagonal lifts to an original diagonal distinct from the ear, and dropping its lift recovers it.

**Definition 1.12 (Every completion at centre 1).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], \forall h \in (5 \leq m),\; (\operatorname{hasType}\left(\operatorname{earOneEquiv}\left(h\right), \operatorname{Equiv}\left(\operatorname{B}\left((m + 1), 1\right), \operatorname{A}\left(m\right)\right)\right) \land ((\forall T \in \operatorname{B}\left((m + 1), 1\right),\; (\operatorname{val}\left(\operatorname{app}\left(\operatorname{earOneEquiv}\left(h\right), T\right)\right) = \operatorname{reduce}\left(\operatorname{val}\left(T\right)\right))) \land (\forall U \in \operatorname{A}\left(m\right),\; (\operatorname{val}\left(\operatorname{app}\left(\operatorname{symm}\left(\operatorname{earOneEquiv}\left(h\right)\right), U\right)\right) = \operatorname{expand}\left(\operatorname{val}\left(U\right)\right)))))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarContraction.earOneEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Deletion and insertion are inverse on the full carriers. The smaller polygon may have five vertices, so the original size may be any size at least six.

**Definition 1.13 (Arbitrary original ear centre).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], \forall i \in \operatorname{ZMod}\left((m + 1)\right),\; \forall h \in (5 \leq m),\; (\operatorname{hasType}\left(\operatorname{earEquiv}\left(h, i\right), \operatorname{Equiv}\left(\operatorname{B}\left((m + 1), i\right), \operatorname{A}\left(m\right)\right)\right) \land ((\forall T \in \operatorname{B}\left((m + 1), i\right),\; (\operatorname{val}\left(\operatorname{app}\left(\operatorname{earEquiv}\left(h, i\right), T\right)\right) = \operatorname{reduce}\left(\operatorname{shiftChords}\left(\operatorname{val}\left(T\right), \operatorname{sub}\left(1, i\right)\right)\right))) \land (\forall U \in \operatorname{A}\left(m\right),\; (\operatorname{val}\left(\operatorname{app}\left(\operatorname{symm}\left(\operatorname{earEquiv}\left(h, i\right)\right), U\right)\right) = \operatorname{shiftChords}\left(\operatorname{expand}\left(\operatorname{val}\left(U\right)\right), \operatorname{sub}\left(i, 1\right)\right)))))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarContraction.earEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Translate by 1-i, apply earOneEquiv, and undo the translation on insertion. This constructs the correspondence for every cyclic placement.

**Definition 1.14 (Pairwise compatible original ears).**

$$\forall n \in Nat,\; \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{Compatible}\left(P\right) \iff (\forall i \in \operatorname{ZMod}\left(n\right),\; \forall j \in \operatorname{ZMod}\left(n\right),\; ((i \in P) \implies ((j \in P) \implies (\operatorname{ne}\left(i, j\right) \implies \operatorname{notCross}\left(\operatorname{ear}\left(i\right), \operatorname{ear}\left(j\right)\right))))))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarContraction.Compatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Distinct selected centres have noncrossing ears. This definition assumes neither a triangulation nor a recursive count.

**Definition 1.15 (Relabel all remaining forced centres).**

$$\forall m \in Nat,\; \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left((m + 1)\right)\right),\; (\operatorname{reducedCenters}\left(P\right) = \operatorname{image}\left(\operatorname{erase}\left(P, 1\right), \operatorname{vertexDrop}\left(\right)\right))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarContraction.reducedCenters` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Erase the selected centre and relabel every other forced centre.

**Theorem 1.16 (Exact number of remaining prescribed centres).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left((m + 1)\right)\right),\; ((6 \leq m) \implies ((1 \in P) \implies (\operatorname{card}\left(\operatorname{reducedCenters}\left(P\right)\right) = \operatorname{natSub}\left(\operatorname{card}\left(P\right), 1\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarContraction.reduced_centres_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Dropping a vertex is injective on the retained centres. Erasing the selected centre therefore decreases the cardinality by exactly one.

**Theorem 1.17 (Compatibility after deletion).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left((m + 1)\right)\right),\; ((6 \leq m) \implies (\operatorname{Compatible}\left(P\right) \implies ((1 \in P) \implies \operatorname{Compatible}\left(\operatorname{reducedCenters}\left(P\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarContraction.reduced_centres_compatible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The other compatible forced ears avoid the deleted centre and its two neighbours. Their chords lift to the original ears, so a crossing after deletion would give an original crossing.

**Definition 1.18 (All other forced ears survive).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left((m + 1)\right)\right),\; \forall h \in (6 \leq m),\; \forall g \in \operatorname{Compatible}\left(P\right),\; \forall b \in (1 \in P),\; (\operatorname{hasType}\left(\operatorname{forcedOneEquiv}\left(h, P, g, b\right), \operatorname{Equiv}\left(\operatorname{H}\left((m + 1), P\right), \operatorname{H}\left(m, \operatorname{reducedCenters}\left(P\right)\right)\right)\right) \land ((\forall T \in \operatorname{H}\left((m + 1), P\right),\; (\operatorname{val}\left(\operatorname{app}\left(\operatorname{forcedOneEquiv}\left(h, P, g, b\right), T\right)\right) = \operatorname{reduce}\left(\operatorname{val}\left(T\right)\right))) \land (\forall U \in \operatorname{H}\left(m, \operatorname{reducedCenters}\left(P\right)\right),\; (\operatorname{val}\left(\operatorname{app}\left(\operatorname{symm}\left(\operatorname{forcedOneEquiv}\left(h, P, g, b\right)\right), U\right)\right) = \operatorname{expand}\left(\operatorname{val}\left(U\right)\right)))))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarContraction.forcedOneEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compatibility with ear(1) excludes neighbouring centres 0 and 2. For every other selected centre, all three original vertices survive and the relabelled ear lifts to exactly the original ear. Survival is derived from compatibility.

**Definition 1.19 (Iterated actual deletion).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall h \in (6 \leq \operatorname{natSub}\left(n, \operatorname{card}\left(P\right)\right)),\; \forall g \in \operatorname{Compatible}\left(P\right),\; (\operatorname{hasType}\left(\operatorname{forcedEquiv}\left(P, h, g\right), \operatorname{Equiv}\left(\operatorname{H}\left(n, P\right), \operatorname{A}\left(\operatorname{natSub}\left(n, \operatorname{card}\left(P\right)\right)\right)\right)\right) \land (\operatorname{forcedEquiv}\left(P, h, g\right) = \operatorname{choice}\left(\operatorname{forcedequivexists}\left(n, P, h, g\right)\right)))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarContraction.forcedEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Induction deletes one forced original centre at a time and composes full correspondences. The forced-set cardinality decreases by one. This gives every triangulation of the polygon with n-card(P) vertices, under precisely the displayed remaining-size premise.

**Theorem 1.20 (Compatible centres occupy at most half the boundary).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((6 \leq n) \implies (\operatorname{Compatible}\left(P\right) \implies (\operatorname{mul}\left(2, \operatorname{card}\left(P\right)\right) \leq n)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarContraction.compatible_card_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adjacent ear centres have crossing ears. A compatible set is disjoint from its translate by one, which has the same cardinality. Their union is contained in the n boundary vertices. For n at least fourteen, deleting a compatible forced set leaves at least seven vertices.

## References

- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarContraction.Compatible`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarContraction.boundary_lift_iff`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarContraction.chordDrop`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarContraction.chordLift`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarContraction.compatible_card_bound`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarContraction.earEquiv`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarContraction.earOneEquiv`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarContraction.expand`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarContraction.expand_isTriangulation`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarContraction.expand_reduce`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarContraction.forcedEquiv`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarContraction.forcedOneEquiv`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarContraction.reduce`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarContraction.reduce_expand`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarContraction.reduce_isTriangulation`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarContraction.reducedCenters`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarContraction.reduced_centres_card`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarContraction.reduced_centres_compatible`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarContraction.vertexDrop`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarContraction.vertexLift`
- Dependency: [D5/S3/Geometry/Polygons/PolygonEarSlide](PolygonEarSlide.md)
