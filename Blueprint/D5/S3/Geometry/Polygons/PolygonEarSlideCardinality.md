# Complete conditioned fibres at every cyclic block origin

## Abstract

Exact complete-fibre local polygon ear-slide counts

**Theorem 1.1 (Exact local law with the optional third-ear fibre).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall a \in \operatorname{ZMod}\left(n\right),\; \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall J \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall R \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((14 \leq n) \implies ((J \subseteq \operatorname{EK}\left((P \cup Q)\right)) \implies (\neg ((a \in J)) \implies (((a + 1) \in J) \implies (((a + 2) \in J) \implies ((R \subseteq \operatorname{erase}\left(\operatorname{erase}\left(\operatorname{erase}\left(J, (a + 1)\right), (a + 2)\right), (a + 3)\right)) \implies (\operatorname{Natcard}\left(\operatorname{ConditionFiber}\left(P, Q, J, \operatorname{insert}\left((a + 2), R\right)\right)\right) = (\operatorname{Natcard}\left(\operatorname{ConditionFiber}\left(P, Q, J, \operatorname{insert}\left((a + 1), R\right)\right)\right) + \operatorname{ite}\left(((a + 3) \in J), \operatorname{Natcard}\left(\operatorname{ConditionFiber}\left(P, Q, J, \operatorname{insert}\left((a + 3), \operatorname{insert}\left((a + 1), R\right)\right)\right)\right), 0\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonEarSlideCardinality.condition_fibre_card_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least 14, P and Q are arbitrary forced and forbidden ear-centre sets. J is a subset of E_K(P union Q), a is absent from J, and a+1,a+2 belong to J. R is supported on J with a+1,a+2,a+3 erased. Nat.card counts the complete ConditionFiber subtype of actual maximal noncrossing finite diagonal sets. Thus infeasible and empty fibres are included.

Write s=a+1, t=a+2, u=a+3. The complete fibre with trace R+t is equivalent, by condition_fibre_equiv_at, to the fibre with trace R+s on J with t,u erased. Every member of that reduced fibre contains s and therefore excludes t, since those actual ears cross. Restoring the observations in J leaves only the choice whether u occurs. When u belongs to J, the two disjoint branches are exactly the original full fibres with traces R+s and R+s+u. Otherwise there is just the R+s fibre. Both branch maps preserve the entire original chord set, P, and Q.

This is the local complete-count law (37.8) of the pinned theory AURIC_FIB_ATOM_INTRINSIC_CLASSIFICATION_AND_POLYGON_GEOMETRY, B-37.2, at source revision 7a72936968c08198f04951d1326bfd4dd891e804. The four source cases (|P|,|Q|)=(2,2),(3,3),(2,4),(4,2), with disjoint compatible P,Q, are special cases; these extra restrictions are unnecessary for the local law. Exchanging P and Q gives a separate instance using E_K(Q union P)=E_K(P union Q). No equality between the two sides' weights is asserted or used.

The result supplies neither global conditional-count positivity, normalized strict inequality or its equality case, nor terminal independent nonempty support. It does not formalize the remainder of B-37.2. Natcard in the formula denotes Nat.card, and ite(c,x,y) means x if c holds and y otherwise; EK in the companion document denotes E_K.

## References

- Truth anchor: `D5/S3/Geometry/Polygons/PolygonEarSlideCardinality.condition_fibre_card_at`
- Dependency: [D5/S3/Geometry/Polygons/PolygonEarSlide](PolygonEarSlide.md)
