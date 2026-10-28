# Path connectedness of the original raw-face link quotient

## Abstract

Every raw-face vertex-label quotient of the carrier of full closed barycentric corner triangles is path connected.

**Theorem 1.1 (The original quotient for each vertex label is path connected).**

$$\forall T \in Type,\; \forall topologyT \in TopologicalSpace\left(T\right),\; \forall P \in RawFacePairing\left(T\right),\; \forall nu \in \operatorname{RawFaceLinkPathConnected}.\operatorname{Vertex}\left(P\right),\; PathConnectedSpace\left(Quotient\left(\operatorname{Relation}.\operatorname{EqvGen}.\operatorname{setoid}\left(\operatorname{RawFaceLinkPathConnected}.\operatorname{Step}\left(P, nu\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/RawFaceLinkPathConnected.original_quotient_path_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let T be any type, equip T with any TopologicalSpace structure, let P be any RawFacePairing T, and let nu be any Vertex P. All names Carrier, Point, Step, chi, frame, sigma, cornerPairing, Vertex and label in this description belong to RawFaceLinkPathConnected. The names Corner, Slot, faceVertex, b, J and cornerRel belong to ActualCornerTransport. In particular, Vertex P is the corner-label quotient ActualCornerTransport.Vertex (cornerPairing P); it supplies the index nu and is distinct from the topological quotient in the conclusion.

Raw T is exactly (T x Fin 4) x (Fin 4 -> R), with the product topology from the chosen topology on T, the canonical topology on Fin 4, and the usual real coordinate topology. Carrier P nu consists of pairs ((t,j),beta) satisfying beta(j)=0, every beta(i)>=0, sum_i beta(i)=1, and label P (t,j)=nu. Point P nu is this entire Carrier subtype with its induced topology. Step P x y means that some f differs from x's omitted corner, x's coordinate at f is zero, and y.val is exactly move P f x.val. The space in the conclusion is L=Quotient (Relation.EqvGen.setoid (Step P)), on Point P nu, carrying the quotient topology of that subtype.

The original frame is frame(f)=(finSuccEquiv' f).trans (optionCongr (chi f)), where chi(0) is the identity and chi(f) swaps 0 and 2 for other f. The permutation sigma is obtained by applying frame, the actual faceMap of P and the inverse target frame. The cornerPairing uses P.facePair itself and conjugates P.faceMap by chi at the source and target faces. The identity sigma(faceVertex(f,r))=faceVertex(targetFace,cornerPairing.sigma((t,f),r)) links these two descriptions of the same face identification.

For a fixed original corner tag (t,j), the full closed barycentric triangle beta(j)=0, beta>=0, sum(beta)=1 is convex. The word closed refers to this barycentric triangle in the real coordinate space, with its edges and vertices included; it does not assert closedness of Carrier P nu in the ambient Raw T for an arbitrary topology on T. Its inclusion into Point P nu is continuous because its tag is constant and its coordinate component is the subtype inclusion. Composing with the continuous quotient projection gives paths in L between any points with that tag. This construction works for the arbitrary chosen topology on T.

For an original slot i=((t,f),r), put j=faceVertex(f,r) and choose k different from f and j. The coordinate unit vector delta_k defines an actual Point z with tag b(i); it satisfies the original zero-coordinate guard at f. Its actual pairedPoint w has tag b(J(cornerPairing P,i)) by the sigma/faceVertex identity, and Step P z w holds with this explicit f. Thus z and w have equal images in L. Paths within the two full triangles join any pair of points at the source and target tags through these images, including repeated corner labels.

Equality of the endpoint labels gives a Relation.EqvGen chain for the original cornerRel. Induction on that chain retains the endpoint Points in the same label nu. In the transitive case c~d~e, the first chain gives label P d=nu; a coordinate unit vector at d supplies an actual intermediate Point z in Carrier P nu. The two induction hypotheses are applied to x,z and z,y and their Joined paths are concatenated. Reflexivity uses a same-tag path, symmetry reverses a path, and each generator uses the guarded crossing above. Finally, a representative corner of nu supplies a Point and hence a quotient point, and quotient induction joins arbitrary points of L.

## References

- Truth anchor: `D5/S3/Geometry/Gluing/RawFaceLinkPathConnected.original_quotient_path_connected`
- Dependency: [D5/S3/Geometry/Hyperideal/ActualCornerTransport](../Hyperideal/ActualCornerTransport.md)
- Dependency: [D5/S3/Geometry/Hyperideal/EdgeStarTransitions](../Hyperideal/EdgeStarTransitions.md)
