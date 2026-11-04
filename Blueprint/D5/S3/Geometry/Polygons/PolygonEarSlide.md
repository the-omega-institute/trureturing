# Complete exact traces and conditioned fibres

## Abstract

Actual polygon condition preserving ear slide

**Definition 1.1 (All ears of the actual chord set).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; \forall i \in \operatorname{ZMod}\left(n\right),\; ((i \in \operatorname{EarCenters}\left(T\right)) \iff (\operatorname{ear}\left(i\right) \in T))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlide.EarCenters` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every ear of the complete finite chord set is observed.

**Definition 1.2 (Common compatible ear carrier).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall K \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall i \in \operatorname{ZMod}\left(n\right),\; ((i \in \operatorname{EK}\left(K\right)) \iff (\neg ((i \in K)) \land (\forall k \in \operatorname{ZMod}\left(n\right),\; ((k \in K) \implies \neg (\operatorname{Cross}\left(\operatorname{ear}\left(i\right), \operatorname{ear}\left(k\right)\right))))))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlide.E_K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

EK denotes E_K: centres outside K whose ears cross no ear of K.

**Definition 1.3 (Complete conditioned exact-trace fibre).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall J \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall X \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{ConditionFiber}\left(P, Q, J, X\right) = \{T: \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right) | (\operatorname{IsTriangulation}\left(T\right) \land ((P \subseteq \operatorname{EarCenters}\left(T\right)) \land (\operatorname{Disjoint}\left(Q, \operatorname{EarCenters}\left(T\right)\right) \land (\operatorname{inter}\left(\operatorname{EarCenters}\left(T\right), J\right) = X))))\})$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonEarSlide.ConditionFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

P is forced, Q is forbidden, and the entire observed J trace equals X. The subtype includes infeasible empty fibres.

**Theorem 1.4 (Cyclic translation of all triangulations).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; \forall a \in \operatorname{ZMod}\left(n\right),\; (\operatorname{IsTriangulation}\left(T\right) \implies \operatorname{IsTriangulation}\left(\operatorname{shiftChords}\left(T, a\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.isTriangulation_map_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

shiftChords(T,a) is the finite image of T under the chord map x -> x+a. Diagonal, noncrossing, and maximality conditions are preserved.

**Theorem 1.5 (Forward exact observed-ear trace).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; \forall J \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall R \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((14 \leq n) \implies (\operatorname{IsTriangulation}\left(T\right) \implies ((\operatorname{ear}\left(2\right) \in T) \implies (\neg ((0 \in J)) \implies ((1 \in J) \implies ((2 \in J) \implies ((R \subseteq \operatorname{erase}\left(\operatorname{erase}\left(\operatorname{erase}\left(J, 1\right), 2\right), 3\right)) \implies ((\operatorname{inter}\left(\operatorname{EarCenters}\left(T\right), J\right) = \operatorname{insert}\left(2, R\right)) \implies (\operatorname{inter}\left(\operatorname{EarCenters}\left(\operatorname{phi}\left(T\right)\right), \operatorname{erase}\left(\operatorname{erase}\left(J, 2\right), 3\right)\right) = \operatorname{insert}\left(1, R\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.trace_phi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

J omits 0 and includes 1,2. R is supported on J with 1,2,3 erased. The output retains exactly R and centre 1 on J with 2,3 erased.

**Theorem 1.6 (Inverse exact observed-ear trace).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; \forall J \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall R \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((14 \leq n) \implies (\operatorname{IsTriangulation}\left(T\right) \implies ((\operatorname{ear}\left(1\right) \in T) \implies (\neg ((0 \in J)) \implies ((1 \in J) \implies ((2 \in J) \implies ((R \subseteq \operatorname{erase}\left(\operatorname{erase}\left(\operatorname{erase}\left(J, 1\right), 2\right), 3\right)) \implies ((\operatorname{inter}\left(\operatorname{EarCenters}\left(T\right), \operatorname{erase}\left(\operatorname{erase}\left(J, 2\right), 3\right)\right) = \operatorname{insert}\left(1, R\right)) \implies (\operatorname{inter}\left(\operatorname{EarCenters}\left(\operatorname{psi}\left(T\right)\right), J\right) = \operatorname{insert}\left(2, R\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.trace_psi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same complete J-origin, membership and R-support hypotheses recover exactly R and centre 2 on the original J.

**Theorem 1.7 (Normalized complete conditioned fibre equivalence).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall J \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall R \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((14 \leq n) \implies ((J \subseteq \operatorname{EK}\left((P \cup Q)\right)) \implies (\neg ((0 \in J)) \implies ((1 \in J) \implies ((2 \in J) \implies ((R \subseteq \operatorname{erase}\left(\operatorname{erase}\left(\operatorname{erase}\left(J, 1\right), 2\right), 3\right)) \implies \operatorname{Equiv}\left(\operatorname{ConditionFiber}\left(P, Q, J, \operatorname{insert}\left(2, R\right)\right), \operatorname{ConditionFiber}\left(P, Q, \operatorname{erase}\left(\operatorname{erase}\left(J, 2\right), 3\right), \operatorname{insert}\left(1, R\right)\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.condition_fibre_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

J lies in E_K(P union Q), omits 0 and contains 1,2; R lies in J with 1,2,3 erased. All forced and forbidden conditions are preserved. No cardinality, P/Q disjointness or compatibility premise is needed for this local equivalence.

**Theorem 1.8 (Complete fibre equivalence at every cyclic origin).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall J \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall R \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall a \in \operatorname{ZMod}\left(n\right),\; ((14 \leq n) \implies ((J \subseteq \operatorname{EK}\left((P \cup Q)\right)) \implies (\neg ((a \in J)) \implies (((a + 1) \in J) \implies (((a + 2) \in J) \implies ((R \subseteq \operatorname{erase}\left(\operatorname{erase}\left(\operatorname{erase}\left(J, (a + 1)\right), (a + 2)\right), (a + 3)\right)) \implies \operatorname{Equiv}\left(\operatorname{ConditionFiber}\left(P, Q, J, \operatorname{insert}\left((a + 2), R\right)\right), \operatorname{ConditionFiber}\left(P, Q, \operatorname{erase}\left(\operatorname{erase}\left(J, (a + 2)\right), (a + 3)\right), \operatorname{insert}\left((a + 1), R\right)\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlide.condition_fibre_equiv_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation by cyclic translation includes every origin a, the cyclic seam, and empty fibres. The cardinality theorem in PolygonEarSlideCardinality uses this equivalence to count the complete fibres.

## References

- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.ConditionFiber`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.E_K`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.EarCenters`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.condition_fibre_equiv`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.condition_fibre_equiv_at`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.isTriangulation_map_add`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.trace_phi`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlide.trace_psi`
- Dependency: [D5/S3/Geometry/Polygons/PolygonEarSlideMaps](PolygonEarSlideMaps.md)
