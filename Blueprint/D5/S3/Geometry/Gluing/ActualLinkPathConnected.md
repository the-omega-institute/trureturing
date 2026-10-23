# Path connectedness of the full original actual-link quotient

## Abstract

Every original actual-link vertex-class quotient is path connected in its canonical quotient topology.

**Theorem 1.1 (Every original vertex-class link is path connected).**

$$\forall G \in Group,\; \forall omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; ((Finite\left(omega\right)) \land (DiscreteTopology\left(omega\right))) \implies (PathConnectedSpace\left(QuotientTopology\left(Quotient\left(EqvGenSetoid\left(Step\left(u, v, nu\right)\right)\right), SubtypeTopology\left(Carrier\left(u, v, nu\right), ProductTopology\left(DiscreteCornerTopology\left(omega\right), RealPiTopology\left(Fin\left(4\right)\right)\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/ActualLinkPathConnected.actual_link_path_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be arbitrary, let Omega be finite with its arbitrary right G-op action and discrete topology, and choose arbitrary u, v and any original vertex class nu. Point is the unchanged Carrier subtype from ActualLinkCornerChains, and L is exactly Quotient(EqvGen.setoid(Step u v)); L carries the inherited canonical quotient topology.

For points with one corner tag, the full closed triangle beta(j)=0, beta>=0, sum(beta)=1 is convex. A continuous subtype inclusion followed by the canonical quotient map gives a Joined path in L. For an actual slot ((omega,f),r), choose a unit coordinate k different from the omitted corner j=faceVertex(f,r) and from the crossed face f. The resulting point lies in the original guard, and frozen_face_data together with the unchanged pairedPoint and Step identifies its quotient image with the corresponding point on the actual paired triangle. This is the live common-point bridge for every face and slot, including repeated and self identifications.

For arbitrary representatives, actual_corner_transport is consumed directly with Unit index, the original endpoint tags, zero real weights and B=0. Its actual Follows list is joined by induction using the same-tag paths and the across-face common point; no reachability or relation correspondence is reproved. Quotient induction then supplies paths between arbitrary quotient points, while Quotient.exists_rep and a coordinate unit vector provide nonemptiness without assuming Omega is nonempty. No transitivity, generation, freeness, regularity, faithfulness or no-self-gluing assumption is introduced.

## References

- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkPathConnected.actual_link_path_connected`
- Dependency: [D5/S3/Geometry/Gluing/ActualLinkCornerChains](ActualLinkCornerChains.md)
