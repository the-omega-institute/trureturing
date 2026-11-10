# Path components of the full original retained quotient

## Abstract

Paths in the original retained quotient correspond exactly to generated orbits of its tetrahedron tags.

**Theorem 1.1 (Joined representatives and generated tag orbits).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] [TopologicalSpace\left(Omega\right)] [DiscreteTopology\left(Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall a \in TruncatedPoint\left(Omega\right),\; \forall b \in TruncatedPoint\left(Omega\right),\; Joined\left(q\left(u, v, a\right), q\left(u, v, b\right)\right) \iff \exists g \in SubgroupClosure\left(pairSet\left(u, v\right)\right),\; act\left(first\left(a\right), g\right) = first\left(b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/ActualTruncatedPathComponents.actual_truncated_joined_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G and Omega be arbitrary types, let G have a Group structure, let the opposite group act on Omega, and equip Omega with a TopologicalSpace structure and its DiscreteTopology hypothesis. The anonymous instance brackets in the formula denote these four dictionaries in their Lean telescope order. Write act(x,g)=op(g) acting on x, so act(act(x,g),h)=act(x,g*h). Choose arbitrary u,v in G and arbitrary actual retained points a,b. Put H(u,v)=Subgroup.closure ({u,v} : Set G), the ordinary generated subgroup. In the displayed formula, pairSet(u,v) denotes exactly this two-element generating set, SubgroupClosure denotes Subgroup.closure, and first denotes the original tag projection.

All carrier and gluing names here are those of ActualLinkAffineFan. Its TruncatedTetrahedron is the subtype of functions p:Fin(4)->R satisfying 0<=p(i)<=3/4 for every i and sum_i p(i)=1. TruncatedPoint Omega is exactly Omega times this entire subtype. The four cap faces p(i)=3/4 remain included. This product has the chosen discrete topology on Omega and the inherited usual real topology on the coordinate subtype.

The original faceWord table is [u,v,v inverse,u inverse]. The original whole-face permutations facePerm have images [3,0,1,2], [3,2,0,1], [2,3,1,0] and [1,2,3,0], respectively. The map truncatedMove(u,v,f) sends (x,p) to (act(x,faceWord(u,v,f)),p composed with facePerm(f) inverse). TruncatedStep(u,v,a,b) requires a face f with a's coordinate at f exactly zero and b exactly this moved point. TruncatedQuotient(u,v,Omega) is the Quotient of Relation.EqvGen.setoid of this TruncatedStep on the full TruncatedPoint carrier. Its topology is the quotient topology of the original product and subtype topology. The projection q in the formula is precisely Quotient.mk for this setoid.

The coordinate carrier is the intersection of the pointwise interval [0,3/4] and the affine hyperplane sum(p)=1. Convexity of intervals, convexity of a linear hyperplane and intersection of convex sets give its convexity. Convex.isPathConnected supplies paths between any two of its points. At a fixed tag x, the map p -> q(x,p) is continuous, so any two full retained points with the same tag have joined images. The argument retains the cap endpoints of these paths.

For each actual face f and tag x, take z=(x,p_f), where p_f(f)=0 and p_f(i)=1/3 for i different from f. Every coordinate lies between zero and 3/4, and the four coordinates sum to one. The exact zero guard enables TruncatedStep from z to truncatedMove(u,v,f,z); hence their original quotient images agree. A same-tag path from any source point to z, this equality, and a same-tag path from the moved point to any target point join arbitrary points whose tags differ by faceWord(u,v,f). Faces zero and one give the two original generators u and v.

Subgroup.closure_induction extends these joins to every g in H(u,v). The identity uses a same-tag path. A product g*h uses the actual intermediate retained point (act(a.first,g),a.second) and concatenates the two paths in the right-action order. An inverse reverses the path obtained by acting with g from the tag act(a.first,g inverse). Stabilizers and repeated tags are allowed in every step.

For the converse, fix the starting tag a.first and define P(x) by the existence of g in H(u,v) with act(a.first,g)=x. Right multiplication by any h in H preserves P in both directions: multiply the witness by h in the forward direction and by h inverse in the reverse direction. Every original faceWord belongs to H, including the two inverse words. Thus P of the tag is invariant under every original TruncatedStep and, by reflexivity, symmetry and transitivity, under the entire original EqvGen with all its intermediate points.

The Bool-valued characteristic of P on TruncatedPoint is continuous because it factors through the discrete original tag space. Its invariance gives a well-defined map L from the original quotient to discrete Bool. Continuous.quotient_lift proves continuity of L for that quotient topology. A path from q(a) to q(b), followed by L, is constant on the preconnected unit interval. Its starting value is true because the identity belongs to H. Its ending value is therefore true, which is exactly the required generated-orbit witness for b.first.

For the whole-space connectedness assertion of Section 122.1, assume explicitly that Omega is nonempty and that H(u,v) acts transitively: for every x,y there is g in H with act(x,g)=y. A chosen tag x and the retained center p(i)=1/4 give a point q(x,p) of the original quotient. Quotient induction and the displayed equivalence join every pair of quotient points, yielding PathConnectedSpace and hence ConnectedSpace. In Section 122.1 the hypothesis G=<u,v> identifies H with G, so the stated transitive action provides the required orbit witness. Finiteness plays no role in this connectedness implication.

The nonempty condition is essential for PathConnectedSpace. When Omega is Empty the retained carrier and quotient are empty, so the pairwise equivalence is vacuous while PathConnectedSpace fails. For a trivial action on Bool there are exactly two path components, one for each tag, despite the nonempty coordinate carrier. For a trivial action on Unit the quotient is path connected. Infinite discrete tag sets satisfy the same component equivalence; no faithfulness, freeness or trivial-stabilizer hypothesis is used.

## References

- Truth anchor: `D5/S3/Geometry/Gluing/ActualTruncatedPathComponents.actual_truncated_joined_iff`
- Dependency: [D5/S3/Geometry/Gluing/ActualLinkAffineFan](ActualLinkAffineFan.md)
