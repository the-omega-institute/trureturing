# Actual polygon carrier and complete conditioned fibres

## Abstract

Actual polygon condition preserving ear slide

**Definition 1.1 (Segments).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{IsSegment}\left(e\right) \iff \neg (\operatorname{IsDiag}\left(e\right)))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlide.IsSegment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A segment has distinct endpoints in the symmetric square.

**Definition 1.2 (Boundary sides).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{IsSide}\left(e\right) \iff \exists i \in \operatorname{ZMod}\left(n\right),\; (e = \operatorname{symPair}\left(i, (i + 1)\right)))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlide.IsSide` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An unordered boundary side joins successive cyclic vertices.

**Definition 1.3 (Internal diagonals).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{IsDiagonal}\left(e\right) \iff (\operatorname{IsSegment}\left(e\right) \land \neg (\operatorname{IsSide}\left(e\right))))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlide.IsDiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Internal diagonals are segments that are not boundary sides.

**Definition 1.4 (Actual cyclic crossing).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall f \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{Cross}\left(e, f\right) \iff \exists a \in \operatorname{ZMod}\left(n\right),\; \exists b \in \operatorname{ZMod}\left(n\right),\; \exists c \in \operatorname{ZMod}\left(n\right),\; \exists d \in \operatorname{ZMod}\left(n\right),\; ((e = \operatorname{symPair}\left(a, b\right)) \land ((f = \operatorname{symPair}\left(c, d\right)) \land (\operatorname{sbtw}\left(a, c, b\right) \land \operatorname{sbtw}\left(b, d, a\right)))))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlide.Cross` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Crossing uses strict cyclic betweenness witnesses.

**Definition 1.5 (Maximal noncrossing finite diagonal carrier).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; (\operatorname{IsTriangulation}\left(T\right) \iff (\forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((e \in T) \implies \operatorname{IsDiagonal}\left(e\right)) \land (\forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall f \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((e \in T) \implies ((f \in T) \implies \neg (\operatorname{Cross}\left(e, f\right)))) \land \forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{IsDiagonal}\left(e\right) \implies (\neg ((e \in T)) \implies \exists f \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((f \in T) \land \operatorname{Cross}\left(e, f\right)))))))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlide.IsTriangulation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier contains every maximal noncrossing finite set of internal diagonals; no completion is selected.

**Definition 1.6 (Ear diagonal at a cyclic centre).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall i \in \operatorname{ZMod}\left(n\right),\; (\operatorname{ear}\left(i\right) = \operatorname{symPair}\left((i - 1), (i + 1)\right))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlide.ear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The local names sEar, tEar, uEar denote ear(1), ear(2), ear(3).

**Definition 1.7 (All ears of the actual chord set).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; \forall i \in \operatorname{ZMod}\left(n\right),\; ((i \in \operatorname{EarCenters}\left(T\right)) \iff (\operatorname{ear}\left(i\right) \in T))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlide.EarCenters` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every ear of the complete finite chord set is observed.

**Definition 1.8 (Common compatible ear carrier).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall K \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall i \in \operatorname{ZMod}\left(n\right),\; ((i \in \operatorname{EK}\left(K\right)) \iff (\neg ((i \in K)) \land \forall k \in \operatorname{ZMod}\left(n\right),\; ((k \in K) \implies \neg (\operatorname{Cross}\left(\operatorname{ear}\left(i\right), \operatorname{ear}\left(k\right)\right)))))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlide.E_K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

EK denotes E_K: centres outside K whose ears cross no ear of K.

**Definition 1.9 (Complete conditioned exact-trace fibre).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall J \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall X \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{ConditionFiber}\left(P, Q, J, X\right) = \{T: \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right) | (\operatorname{IsTriangulation}\left(T\right) \land ((P \subseteq \operatorname{EarCenters}\left(T\right)) \land (\operatorname{Disjoint}\left(Q, \operatorname{EarCenters}\left(T\right)\right) \land (\operatorname{inter}\left(\operatorname{EarCenters}\left(T\right), J\right) = X))))\})$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlide.ConditionFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

P is forced, Q is forbidden, and the entire observed J trace equals X. The subtype includes infeasible empty fibres.

**Definition 1.10 (Exchange the two local vertices).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall i \in \operatorname{ZMod}\left(n\right),\; (\operatorname{vertexSwap}\left(n, i\right) = \operatorname{swap}\left(1, 2, i\right))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlide.vertexSwap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vertex permutation exchanges 1 and 2 and fixes every other vertex.

**Definition 1.11 (Induced unordered-chord exchange).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{chordSwap}\left(e\right) = \operatorname{map}\left(\operatorname{vertexSwap}\left(n\right), e\right))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlide.chordSwap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Symmetric-square map transports each unordered pair.

**Definition 1.12 (Avoid the deleted centre).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{AvoidTwo}\left(e\right) \iff \forall x \in \operatorname{ZMod}\left(n\right),\; \neg ((e = \operatorname{symPair}\left(2, x\right))))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlide.AvoidTwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every endpoint avoids vertex 2.

**Theorem 1.13 (Cyclic translation of all triangulations).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; \forall a \in \operatorname{ZMod}\left(n\right),\; (\operatorname{IsTriangulation}\left(T\right) \implies \operatorname{IsTriangulation}\left(\operatorname{shiftChords}\left(T, a\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.isTriangulation_map_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

shiftChords(T,a) is the finite image of T under the chord map x -> x+a. Diagonal, noncrossing, and maximality conditions are preserved.

**Theorem 1.14 (Crossing transport away from centre 2).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall f \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((6 \leq n) \implies (\operatorname{AvoidTwo}\left(e\right) \implies (\operatorname{AvoidTwo}\left(f\right) \implies (\operatorname{Cross}\left(\operatorname{chordSwap}\left(e\right), \operatorname{chordSwap}\left(f\right)\right) \iff \operatorname{Cross}\left(e, f\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.cross_chordSwap_of_avoidTwo` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Crossing is transported in both directions, including across the cyclic seam.

**Theorem 1.15 (Ear-centre exclusion).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; \forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((6 \leq n) \implies (\operatorname{IsTriangulation}\left(T\right) \implies ((\operatorname{ear}\left(2\right) \in T) \implies ((e \in T) \implies \operatorname{AvoidTwo}\left(e\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.avoidTwo_of_mem_triangulation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A triangulation containing t has no internal diagonal incident with its centre 2.

**Definition 1.16 (Forward complete chord map).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; (\operatorname{phi}\left(T\right) = \operatorname{insert}\left(\operatorname{ear}\left(1\right), \operatorname{image}\left(chordSwap, \operatorname{erase}\left(T, \operatorname{ear}\left(2\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlide.phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Erase t, exchange vertices 1 and 2 in every retained chord, and insert s.

**Definition 1.17 (Inverse complete chord map).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; (\operatorname{psi}\left(T\right) = \operatorname{insert}\left(\operatorname{ear}\left(2\right), \operatorname{image}\left(chordSwap, \operatorname{erase}\left(T, \operatorname{ear}\left(1\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlide.psi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Erase s, apply the same vertex exchange, and insert t.

**Theorem 1.18 (Forward actual triangulation preservation).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; ((6 \leq n) \implies (\operatorname{IsTriangulation}\left(T\right) \implies ((\operatorname{ear}\left(2\right) \in T) \implies \operatorname{IsTriangulation}\left(\operatorname{phi}\left(T\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.phi_isTriangulation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Diagonal and crossing preservation use ear-centre exclusion; maximality handles the fresh s separately.

**Theorem 1.19 (Inverse actual triangulation preservation).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; ((6 \leq n) \implies (\operatorname{IsTriangulation}\left(T\right) \implies ((\operatorname{ear}\left(1\right) \in T) \implies \operatorname{IsTriangulation}\left(\operatorname{psi}\left(T\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.psi_isTriangulation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse preserves the full maximal diagonal carrier.

**Theorem 1.20 (Left inverse on complete chord sets).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; ((6 \leq n) \implies (\forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((e \in T) \implies \operatorname{IsDiagonal}\left(e\right)) \implies ((\operatorname{ear}\left(2\right) \in T) \implies (\neg ((\operatorname{ear}\left(1\right) \in T)) \implies (\operatorname{psi}\left(\operatorname{phi}\left(T\right)\right) = T)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.psi_phi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse law requires only diagonal membership and the stated included and excluded ears.

**Theorem 1.21 (Right inverse on complete chord sets).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; ((6 \leq n) \implies (\forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((e \in T) \implies \operatorname{IsDiagonal}\left(e\right)) \implies ((\operatorname{ear}\left(1\right) \in T) \implies (\neg ((\operatorname{ear}\left(2\right) \in T)) \implies (\operatorname{phi}\left(\operatorname{psi}\left(T\right)\right) = T)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.phi_psi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality holds for the entire finite chord set.

**Theorem 1.22 (Forward exact observed-ear trace).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; \forall J \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall R \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((14 \leq n) \implies (\operatorname{IsTriangulation}\left(T\right) \implies ((\operatorname{ear}\left(2\right) \in T) \implies (\neg ((0 \in J)) \implies ((1 \in J) \implies ((2 \in J) \implies ((R \subseteq \operatorname{erase}\left(\operatorname{erase}\left(\operatorname{erase}\left(J, 1\right), 2\right), 3\right)) \implies ((\operatorname{inter}\left(\operatorname{EarCenters}\left(T\right), J\right) = \operatorname{insert}\left(2, R\right)) \implies (\operatorname{inter}\left(\operatorname{EarCenters}\left(\operatorname{phi}\left(T\right)\right), \operatorname{erase}\left(\operatorname{erase}\left(J, 2\right), 3\right)\right) = \operatorname{insert}\left(1, R\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.trace_phi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

J omits 0 and includes 1,2. R is supported on J with 1,2,3 erased. The output retains exactly R and centre 1 on J with 2,3 erased.

**Theorem 1.23 (Inverse exact observed-ear trace).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; \forall J \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall R \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((14 \leq n) \implies (\operatorname{IsTriangulation}\left(T\right) \implies ((\operatorname{ear}\left(1\right) \in T) \implies (\neg ((0 \in J)) \implies ((1 \in J) \implies ((2 \in J) \implies ((R \subseteq \operatorname{erase}\left(\operatorname{erase}\left(\operatorname{erase}\left(J, 1\right), 2\right), 3\right)) \implies ((\operatorname{inter}\left(\operatorname{EarCenters}\left(T\right), \operatorname{erase}\left(\operatorname{erase}\left(J, 2\right), 3\right)\right) = \operatorname{insert}\left(1, R\right)) \implies (\operatorname{inter}\left(\operatorname{EarCenters}\left(\operatorname{psi}\left(T\right)\right), J\right) = \operatorname{insert}\left(2, R\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.trace_psi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same complete J-origin, membership and R-support hypotheses recover exactly R and centre 2 on the original J.

**Theorem 1.24 (Normalized complete conditioned fibre equivalence).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall J \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall R \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((14 \leq n) \implies ((J \subseteq \operatorname{EK}\left((P \cup Q)\right)) \implies (\neg ((0 \in J)) \implies ((1 \in J) \implies ((2 \in J) \implies ((R \subseteq \operatorname{erase}\left(\operatorname{erase}\left(\operatorname{erase}\left(J, 1\right), 2\right), 3\right)) \implies \operatorname{Equiv}\left(\operatorname{ConditionFiber}\left(P, Q, J, \operatorname{insert}\left(2, R\right)\right), \operatorname{ConditionFiber}\left(P, Q, \operatorname{erase}\left(\operatorname{erase}\left(J, 2\right), 3\right), \operatorname{insert}\left(1, R\right)\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.condition_fibre_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

J lies in E_K(P union Q), omits 0 and contains 1,2; R lies in J with 1,2,3 erased. All forced and forbidden conditions are preserved. No cardinality, P/Q disjointness or compatibility premise is needed for this local equivalence.

**Theorem 1.25 (Complete fibre equivalence at every cyclic origin).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall J \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall R \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall a \in \operatorname{ZMod}\left(n\right),\; ((14 \leq n) \implies ((J \subseteq \operatorname{EK}\left((P \cup Q)\right)) \implies (\neg ((a \in J)) \implies (((a + 1) \in J) \implies (((a + 2) \in J) \implies ((R \subseteq \operatorname{erase}\left(\operatorname{erase}\left(\operatorname{erase}\left(J, (a + 1)\right), (a + 2)\right), (a + 3)\right)) \implies \operatorname{Equiv}\left(\operatorname{ConditionFiber}\left(P, Q, J, \operatorname{insert}\left((a + 2), R\right)\right), \operatorname{ConditionFiber}\left(P, Q, \operatorname{erase}\left(\operatorname{erase}\left(J, (a + 2)\right), (a + 3)\right), \operatorname{insert}\left((a + 1), R\right)\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.condition_fibre_equiv_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation by cyclic translation includes every origin a, the cyclic seam, and empty fibres. The cardinality theorem in PolygonEarSlideCardinality consumes this equivalence on its live proof path.

## References

- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.AvoidTwo`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.ConditionFiber`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.Cross`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.E_K`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.EarCenters`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.IsDiagonal`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.IsSegment`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.IsSide`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.IsTriangulation`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.avoidTwo_of_mem_triangulation`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.chordSwap`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.condition_fibre_equiv`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.condition_fibre_equiv_at`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.cross_chordSwap_of_avoidTwo`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.ear`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.isTriangulation_map_add`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.phi`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.phi_isTriangulation`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.phi_psi`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.psi`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.psi_isTriangulation`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.psi_phi`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.trace_phi`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.trace_psi`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.vertexSwap`
