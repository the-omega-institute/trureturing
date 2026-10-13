# Actual guarded corner chains

## Abstract

Original affine link chains: exact point classes and strict-region restriction; compact Hausdorff quotient by ambient closed-relation reuse.

**Definition 1.1 (The original whole-face permutations).**

$$\forall f \in Fin\left(4\right),\; \forall i \in Fin\left(4\right),\; facePerm\left(f, i\right) = lookup\left(((3, 0, 1, 2), (3, 2, 0, 1), (2, 3, 1, 0), (1, 2, 3, 0)), f, i\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.facePerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four rows are p=(3,0,1,2), q=(3,2,0,1), q inverse and p inverse. The source-owned frozen_face_data proof compares these whole-face maps with the published facePair and slotMap on each actual face slot.

**Definition 1.2 (Inverse omitted faces).**

$$\forall f \in Fin\left(4\right),\; reverseFace\left(f\right) = lookup\left((3, 2, 1, 0), f\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.reverseFace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Faces 0 and 3 are paired; faces 1 and 2 are paired.

**Definition 1.3 (The source group words).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall f \in Fin\left(4\right),\; faceWord\left(u, v, f\right) = lookup\left((u, v, inverse\left(v\right), inverse\left(u\right)), f\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.faceWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source-to-target words are u, v, v inverse, u inverse, in omitted-face order. Multiplication retains the published right-action convention.

**Theorem 1.4 (The actual slot map and whole-face extension agree).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall t \in Omega,\; \forall f \in Fin\left(4\right),\; \forall r \in Fin\left(3\right),\; facePair\left(u, v, (t, f)\right) = (act\left(t, faceWord\left(u, v, f\right)\right), reverseFace\left(f\right)) \land apply\left(facePerm\left(f\right), faceVertex\left(f, r\right)\right) = faceVertex\left(reverseFace\left(f\right), slotMap\left(f, r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/ActualLinkCornerChains.frozen_face_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each sheet t, each of the four faces f and each of its three slots r, the original facePair is (act(t,faceWord(u,v,f)),reverseFace(f)), and the whole-face permutation sends faceVertex(f,r) to faceVertex(reverseFace(f),slotMap(f,r)). This source-owned comparison supplies the target corner tag for both the original carrier preservation proof and the common-point construction in ActualLinkPathConnected.

**Definition 1.5 (Tagged barycentric coordinates).**

$$\forall Omega \in Type,\; Raw\left(Omega\right) = Omega \times Fin\left(4\right) \times Functions\left(Fin\left(4\right), R\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Raw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A raw representative has an actual corner (omega,j) and four real barycentric coordinates.

**Definition 1.6 (The complete original corner triangle).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall x \in Raw\left(Omega\right),\; x \in Carrier\left(u, v, nu\right) \Leftrightarrow \left(coordinate\left(x, second\left(corner\left(x\right)\right)\right) = 0 \land \left(\left(\forall i \in Fin\left(4\right),\; 0 \le coordinate\left(x, i\right)\right) \land \left(sumCoordinates\left(x\right) = 1 \land label\left(pairing\left(u, v\right), corner\left(x\right)\right) = nu\right)\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Carrier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate at j is zero, every coordinate is nonnegative, and their sum is one. The actual corner label is the fixed nu from the frozen Pairing quotient. Boundary ties remain in this closed carrier.

**Definition 1.7 (The actual carrier subtype).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; Point\left(u, v, nu\right) = Subtype\left(Carrier\left(u, v, nu\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Point` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Representatives carry all closed-carrier conditions and the same actual corner-class tag.

**Definition 1.8 (Original affine face transport).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall f \in Fin\left(4\right),\; \forall x \in Raw\left(Omega\right),\; move\left(u, v, f, x\right) = ((act\left(first\left(corner\left(x\right)\right), faceWord\left(u, v, f\right)\right), apply\left(facePerm\left(f\right), second\left(corner\left(x\right)\right)\right)), pullback\left(facePerm\left(f\right), coordinates\left(x\right)\right))$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.move` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transport the sheet by the exact source word, the omitted corner by the whole-face permutation, and the coordinate vector by its inverse. No endpoints are sorted.

**Definition 1.9 (A permitted affine image in the same actual corner class).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall x \in Point\left(u, v, nu\right),\; \forall f \in Fin\left(4\right),\; f \neq second\left(corner\left(x\right)\right) \Rightarrow value\left(pairedPoint\left(u, v, x, f\right)\right) = move\left(u, v, f, value\left(x\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.pairedPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input requires f different from the omitted corner j. The carrier proof directly consumes the published actual_step helper at its original owner, after extending the original face-slot table. The sum and coordinate conditions are preserved by the whole-face permutation. This definition constructs the affine image even away from a side; the Step relation separately imposes the zero guard.

**Definition 1.10 (Only the original guarded link generators).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall x \in Point\left(u, v, nu\right),\; \forall y \in Point\left(u, v, nu\right),\; Step\left(u, v, x, y\right) \Leftrightarrow \left(\exists f \in Fin\left(4\right),\; f \neq second\left(corner\left(x\right)\right) \land \left(coordinate\left(x, f\right) = 0 \land value\left(y\right) = move\left(u, v, f, value\left(x\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A step requires f different from j and beta(f)=0, and its target is the displayed affine image. The identically zero omitted-corner coordinate creates no fourth side.

**Definition 1.11 (The full original affine equivalence closure).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall x \in Point\left(u, v, nu\right),\; \forall y \in Point\left(u, v, nu\right),\; Related\left(u, v, x, y\right) \Leftrightarrow EqvGen\left(Step\left(u, v\right), x, y\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Related` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take EqvGen of Step on the entire closed carrier. No chart region, assumed cycle or radial-map kernel defines this relation.

**Definition 1.12 (Ordered endpoint data).**

$$\forall Omega \in Type,\; Dart\left(Omega\right) = Omega \times Fin\left(4\right) \times Fin\left(4\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Dart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The raw ordered occurrence is ((omega,j),k). Actual corner neighborhoods have j different from k because beta(j)=0 and beta(k)>1/2. The data type retains every order, including (3,0).

**Definition 1.13 (The same whole-face transport on ordered endpoints).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall d \in Dart\left(Omega\right),\; \forall f \in Fin\left(4\right),\; dartMove\left(u, v, f, d\right) = ((act\left(sheet\left(d\right), faceWord\left(u, v, f\right)\right), apply\left(facePerm\left(f\right), firstEndpoint\left(d\right)\right)), apply\left(facePerm\left(f\right), secondEndpoint\left(d\right)\right))$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.dartMove` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both j and k move by the actual face permutation; the sheet moves by the actual word.

**Definition 1.14 (Original oriented edge-incidence transport).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall d \in Dart\left(Omega\right),\; \forall e \in Dart\left(Omega\right),\; DartStep\left(u, v, d, e\right) \Leftrightarrow \left(\exists f \in Fin\left(4\right),\; f \neq firstEndpoint\left(d\right) \land \left(f \neq secondEndpoint\left(d\right) \land e = dartMove\left(u, v, f, d\right)\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.DartStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A dart step may use only a face omitting neither endpoint. This is a generated incidence relation, not an assumed cyclic enumeration.

**Definition 1.15 (The actual ordered-dart component).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall d \in Dart\left(Omega\right),\; \forall e \in Dart\left(Omega\right),\; DartRelated\left(u, v, d, e\right) \Leftrightarrow EqvGen\left(DartStep\left(u, v\right), d, e\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.DartRelated` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The equivalence closure is generated by the actual guarded endpoint moves. This delivery does not enumerate its component by Fin(3r).

**Definition 1.16 (Strict corner regions from an actual endpoint component).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall d \in Dart\left(Omega\right),\; \forall x \in Point\left(u, v, nu\right),\; x \in Neighborhood\left(u, v, d\right) \Leftrightarrow \left(\exists k \in Fin\left(4\right),\; \frac{1}{2} < coordinate\left(x, k\right) \land DartRelated\left(u, v, d, (corner\left(x\right), k)\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Neighborhood` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A representative is selected when some beta(k)>1/2 and its ordered dart is in the actual component of the selected seed. The strict inequality excludes boundary ties from this region while retaining them in Carrier. This delivery proves saturation and chain reflection; it does not yet prove openness or a disk coordinate.

**Definition 1.17 (Interior coordinates).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall x \in Point\left(u, v, nu\right),\; Interior\left(x\right) \Leftrightarrow \left(\forall f \in Fin\left(4\right),\; f \neq second\left(corner\left(x\right)\right) \Rightarrow coordinate\left(x, f\right) \neq 0\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Interior` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every non-omitted coordinate is nonzero. On the nonnegative closed carrier this means each of those three coordinates is positive.

**Definition 1.18 (A unique active side).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall x \in Point\left(u, v, nu\right),\; \forall f \in Fin\left(4\right),\; EdgePoint\left(x, f\right) \Leftrightarrow \left(f \neq second\left(corner\left(x\right)\right) \land \left(coordinate\left(x, f\right) = 0 \land \left(\forall g \in Fin\left(4\right),\; \left(g \neq second\left(corner\left(x\right)\right) \land coordinate\left(x, g\right) = 0\right) \Rightarrow g = f\right)\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.EdgePoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exactly one non-omitted coordinate is zero. The other two are nonzero and, on this carrier, positive.

**Theorem 1.19 (Source-specific normal forms and full-chain restriction).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall x \in Point\left(u, v, nu\right),\; \forall y \in Point\left(u, v, nu\right),\; \left(Interior\left(x\right) \Rightarrow \left(Related\left(u, v, x, y\right) \Leftrightarrow y = x\right)\right) \land \left(\left(\forall f \in Fin\left(4\right),\; EdgePoint\left(x, f\right) \Rightarrow \left(pairedPoint\left(u, v, x, f\right) \neq x \land \left(Related\left(u, v, x, y\right) \Leftrightarrow \left(y = x \lor y = pairedPoint\left(u, v, x, f\right)\right)\right)\right)\right) \land \left(\left(\forall d \in Dart\left(Omega\right),\; Related\left(u, v, x, y\right) \Rightarrow \left(x \in Neighborhood\left(u, v, d\right) \Leftrightarrow y \in Neighborhood\left(u, v, d\right)\right)\right) \land \left(\forall d \in Dart\left(Omega\right),\; \left(x \in Neighborhood\left(u, v, d\right) \land y \in Neighborhood\left(u, v, d\right)\right) \Rightarrow \left(Related\left(u, v, x, y\right) \Leftrightarrow EqvGen\left(StepRestrictedTo\left(u, v, Neighborhood\left(u, v, d\right)\right), subtype\left(x\right), subtype\left(y\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/ActualLinkCornerChains.actual_guarded_point_analysis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every group, arbitrary right action, u and v, actual corner class nu, and original representatives x and y: an interior x has singleton class; an EdgePoint has exactly x and its distinct original paired image as its class; every strict component neighborhood is invariant under the full EqvGen; and restriction to that neighborhood reflects the full relation. The positive-side proof constructs a two-point invariant from the unique active guard and inverse pairing. It then inducts through all four EqvGen constructors. Saturation is established before the restriction proof, whose transitive case explicitly transports membership to the intermediate representative. These are new original-carrier deductions, not applications of an assumed cycle or assumed relation correspondence. The helpers are consumed on these live proof paths. The remaining local obligations are the four minimal point-period Fin(3r) enumerations, the exact origin-cycle and fan-seam correspondence, openness with the actual quotient-subspace topology, the supplied fan radial chart at the same actual vertex, and the geometric truncation-slice chain and topology comparison. Global orientability, genus, marked-manifold realization and metric statements remain outside this result. No external novelty is claimed.

Application: compactness and Hausdorff separation of the full original link quotient. Let G be any group, let Omega be a finite set with the discrete topology, and let G act on the right on Omega, represented in Lean by MulAction Gᵐᵒᵖ Omega. Fix arbitrary u,v in G and nu in Vertex(pairing u v). Use `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Carrier` and `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Point` exactly as defined above: x=((omega,j),beta) has beta(j)=0, beta(i)>=0 for every i, sum beta=1, and label(pairing u v,(omega,j))=nu. The real coordinate space has its product topology, Point has the inherited subtype topology, and Q=Point/Related has the topology induced by its quotient projection. This Q is compact and Hausdorff.

For the ambient application put I=Fin 4, T=Omega times Fin 4, Delta=stdSimplex R I, and X=T times Delta. Write raw((omega,j),beta)=((omega,j),beta) for forgetting the simplex proof, and embed:Point -> X for keeping the same tag and coordinates with their simplex membership. Set p_f=facePerm(f) and w_f=faceWord(u,v,f). For f different from j take next((omega,j),f)=(act(omega,w_f),p_f(j)) and sigma((omega,j),f)=p_f. For f=j take next((omega,j),f)=(omega,j) and sigma((omega,j),f)=id. If permute(rho,beta)(i)=beta(rho inverse(i)), define seam(a,b) by the existence of f with beta_a(f)=0 and b=(next(tag_a,f),permute(sigma(tag_a,f),beta_a)). Coordinate reindexing preserves Delta by nonnegativity and permutation invariance of the sum.

The whole-face maps and words have the original source correspondence: frozen_face_data compares facePerm and faceWord with facePair and slotMap at every actual face slot. Thus a seam at f different from j is precisely the raw image in `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Step` with its original zero guard. A seam at f=j is the identity; it adds only reflexivity to the ambient equivalence closure, not another side identification. No change of action convention, endpoint order, or corner label enters this correspondence.

Let C(a) mean raw(a) belongs to Carrier(u,v,nu). Every seam preserves C in both directions. Forward membership is the carrier property of pairedPoint. For a permitted move through f, the original perm_face identity gives reverseFace(f)=p_f(f), so reverseFace(f) differs from the target omitted corner p_f(j). Applying pairedPoint at that reverse face preserves the target carrier; the original move_inverse identity recovers raw(a). These are the private source facts already used by the original guarded-chain analysis. Identity seams preserve C immediately.

To restrict whole ambient chains, define E(a,b) as the conjunction of C(a) iff C(b) and the assertion that, for every ha:C(a) and hb:C(b), Related(u,v,(raw(a),ha),(raw(b),hb)) holds. E is an equivalence relation: reflexivity and symmetry use the corresponding Related laws; transitivity composes the membership equivalences and the Related proofs. In the transitive case E(a,b), E(b,c), membership ha:C(a) supplies hb:C(b) through the first equivalence before the two subtype relations are composed. This does not assume that arbitrary ambient intermediate points already lie in Carrier.

Each seam lies in E by the preceding membership fact and either Related reflexivity or the original Step constructor. Apply the pinned Relation.EqvGen.eqvGen_le from Mathlib.Logic.Relation with r=seam and r'=E: minimality of equivalence closure gives EqvGen(seam) <= E. Conversely the pullback R(x,y)=EqvGen(seam)(embed(x),embed(y)) is an equivalence relation by IsEquiv.comap, and every original Step lies in R by its displayed affine formula. The same eqvGen_le, now with r=Step and r'=R, gives Related <= R. Projecting the first application onto points of Carrier gives R <= Related. Hence Related(x,y) iff EqvGen(seam)(embed(x),embed(y)) for every pair in the entire original closed carrier.

Apply `D5/S3/Geometry/Gluing/FiniteZeroGuardedClosure.uniform_transport_and_closed_relation` to these exact T,I,Delta,next,sigma. Its closed-relation component says that EqvGen(seam) is closed in X times X. The indexing states consist of two finite tags, a coordinate permutation and a finite zero footprint; finiteness concerns the family of closed pieces, not the set of related pairs. The continuous embed times embed pulls this closed relation back to the original Related set in Point times Point by the equivalence just established.

Point is compact Hausdorff. Carrier is a closed subset of T times Delta: the omitted coordinate equation beta(j)=0 is closed because the finite discrete tag makes j locally constant, and the fixed label condition is closed in the discrete corner tags. The simplex supplies the nonnegative coordinates and sum equation. Finite T and the closed real standard simplex are compact, so their closed subset is compact by isCompact_stdSimplex and the closed-subset API. The ambient discrete tag and real product spaces are Hausdorff, and so is the subtype Point.

Let q:Point -> Q be the original quotient map. For a closed subset A of Point, its saturation q inverse(q(A)) is the second projection of Related intersect (A times Point). This intersection is closed in the compact product Point times Point; its image is compact and therefore closed in Hausdorff Point. The quotient-topology criterion then makes q a closed map. Each fiber of q is the closed Related class of a representative and is compact. The pinned isProperMap_iff_isClosedMap_and_compact_fibers therefore makes q proper without presupposing that Q is Hausdorff.

IsProperMap.prodMap makes q times q proper and hence closed. It is continuous and surjective, so IsClosedMap.isQuotientMap makes it a quotient map. Its inverse image of the diagonal of Q is exactly Related, already closed; the quotient-map closed-preimage criterion and t2_iff_isClosed_diagonal give T2Space Q. Independently, the continuous surjection q carries compact Point onto Q, giving CompactSpace Q. These steps use the original subtype and quotient topologies throughout.

The application includes all four omitted corners, boundary ties, every actual corner class and degenerate action fibers. The group may be noncommutative; the action need not be faithful, regular, free, transitive or generated by u and v. It supplies compactness and Hausdorffness of this exact quotient. Connectedness, local disk charts, orientability, Euler characteristic, genus and the comparison with a geometric truncation slice require their respective additional arguments.

## References

- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Carrier`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Carrier`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Dart`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.DartRelated`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.DartStep`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.EdgePoint`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Interior`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Neighborhood`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Point`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Point`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Raw`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Related`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Step`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Step`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.actual_guarded_point_analysis`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.dartMove`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.facePerm`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.faceWord`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.frozen_face_data`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.move`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.pairedPoint`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.reverseFace`
- Truth anchor: `D5/S3/Geometry/Gluing/FiniteZeroGuardedClosure.uniform_transport_and_closed_relation`
- Dependency: [D5/S3/Geometry/Hyperideal/NoncommutativeCornerOrbits](../Hyperideal/NoncommutativeCornerOrbits.md)
