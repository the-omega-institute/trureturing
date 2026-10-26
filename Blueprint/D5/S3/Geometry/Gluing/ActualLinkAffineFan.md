# Actual strict-sector affine coordinates

## Abstract

Actual ordered-corner occurrences carry strict affine sector coordinates.

**Definition 1.1 (The strict triangle sector).**

$$\forall p \in Real \times Real,\; member\left(p, Sector\right) \Leftrightarrow \left(0 \le first\left(p\right) \land \left(0 \le second\left(p\right) \land add\left(first\left(p\right), second\left(p\right)\right) < 1\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.Sector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two real coordinates are nonnegative and their sum is strictly less than one. This is the open radial part of the closed triangle, with both seam edges and the origin retained.

**Definition 1.2 (Source barycentric coordinates).**

$$\forall c \in Fin\left(4\right),\; \forall s \in Fin\left(3\right),\; \forall p \in Real \times Real,\; \forall l \in Fin\left(4\right),\; beta\left(c, s, p, l\right) = if\left(l = tip\left(c, s\right), subtract\left(1, divide\left(add\left(first\left(p\right), second\left(p\right)\right), 2\right)\right), if\left(l = incoming\left(c, s\right), divide\left(first\left(p\right), 2\right), if\left(l = outgoing\left(c, s\right), divide\left(second\left(p\right), 2\right), 0\right)\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.beta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For row c and phase s, the omitted corner has coordinate zero, the ordered tip has coordinate 1-(a+b)/2, the incoming face has a/2, and the outgoing face has b/2. The four labels are distinct in each of the twelve actual ordered endpoint positions.

**Definition 1.3 (The actual seed corner class).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall x \in Omega,\; vertex\left(u, v, c, x\right) = label\left(pairing\left(u, v\right), first\left(encode\left(u, v, c, (x, 0)\right)\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vertex is the original pairing label of the corner of encode(u,v,c,(x,0)). All four rows retain the source order L0, L1, H2, H0, and ordered pairs such as (3,0) are not sorted.

**Definition 1.4 (Finite occurrence coordinates).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall x \in Omega,\; \forall z \in Fin\left(3 \times pointPeriod\left(u, v, c, x\right)\right) \times Sector,\; rawPhi\left(u, v, c, x, z\right) = (first\left(occurrence\left(u, v, c, x, first\left(z\right)\right)\right), beta\left(c, second\left(iterate\left(tour\left(u, v, c\right), value\left(first\left(z\right)\right), (x, 0)\right)\right), value\left(second\left(z\right)\right)\right))$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.rawPhi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index lies in Fin(3r), where r is the minimal point period of the original row return word at x. Its actual dart is occurrence(u,v,c,x,i). The phase of the corresponding iterate of tour determines the incoming and outgoing face coordinates. No return of the full transported frame is required.

**Definition 1.5 (The strict original neighborhood).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall x \in Omega,\; Finite\left(Omega\right) \Rightarrow \left(\forall z \in Fin\left(3 \times pointPeriod\left(u, v, c, x\right)\right) \times Sector,\; member\left(Phi\left(u, v, c, x, z\right), Neighborhood\left(u, v, vertex\left(u, v, c, x\right), encode\left(u, v, c, (x, 0)\right)\right)\right) \land underlyingRaw\left(Phi\left(u, v, c, x, z\right)\right) = (first\left(occurrence\left(u, v, c, x, first\left(z\right)\right)\right), beta\left(c, second\left(iterate\left(tour\left(u, v, c\right), value\left(first\left(z\right)\right), (x, 0)\right)\right), value\left(second\left(z\right)\right)\right))\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.Phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrict a and b to nonnegative reals with a+b<1. The constructed raw point lies in the original Carrier at the actual seed vertex and in Neighborhood of the actual seed dart. Its ordered tip has barycentric coordinate strictly greater than one half. The cutoff a+b=1 is outside this chart; it is not removed from the ambient carrier.

**Theorem 1.6 (Unique actual occurrence and affine coordinates).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall x \in Omega,\; Finite\left(Omega\right) \Rightarrow Bijective\left(Phi\left(u, v, c, x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actual_strict_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any group G, any finite set Omega with a right G action, any u and v, any one of the four rows, and any root x, Phi bijectively parametrizes the genuine strict original neighborhood. There is no assumption that G is finite, that the action is faithful, free, transitive or regular, or that the return word has finite group order.

The inverse first finds the unique barycentric coordinate greater than one half. The original ordered-dart component enumeration then determines the unique occurrence index. The two real coordinates are twice the original incoming and outgoing barycentric coordinates. The simplex equation and zero omitted-corner coordinate prove that their sum is strictly less than one and reconstruct every original barycentric entry.

The original pairedPoint construction transports the corner label along each guarded dart step; EqvGen induction transports it along the complete dart component. This puts Phi at the same actual link vertex, not at an independently chosen label. The finite-period supplier covers singleton period one, giving three occurrences, as well as nonfaithful and nonregular actions.

The guarded generator calculation below identifies exactly the positive strict-sector seams and their reverses. Full original chains reflect to the strict neighborhood before being transported through the coordinate bijection. The topology below is induced from the original discrete corner labels and real barycentric coordinates. The closed fan comparison below reflects every intermediate chain through the strict radius cutoff. The exact original radial norm identity now supplies the closed-fan restriction and the open unit disk chart. The literal affine cap map below also identifies the full original corner carrier and relation with its cap image in the full original truncated quotient. Global orientability, closedness, genus and geometric conclusions remain separate.

The source is the actual link application accompanying supplement 122.3 of the group-transport construction. ActualCornerPointPeriods supplies the entire original dart component, and ActualLinkCornerChains supplies the original guarded affine carrier. The cyclic fan disk theorem is an existing further supplier; no generic circle or disk theorem is proved here. No literature-priority claim is made.

**Definition 1.7 (Positive point-period sector count).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall x \in Omega,\; Finite\left(Omega\right) \Rightarrow NeZero\left(3 \times pointPeriod\left(u, v, c, x\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.sector_count_neZero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual point period is positive. Consequently the cyclic index type Fin(3r) has nonzero size, including r=1.

**Definition 1.8 (Exchange of seam coordinates).**

$$\forall p \in Sector,\; value\left(swap\left(p\right)\right) = (second\left(value\left(p\right)\right), first\left(value\left(p\right)\right))$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.swap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Swapping a and b preserves nonnegativity and the strict radial bound.

**Definition 1.9 (Positive cyclic seam).**

$$\forall n \in Nat,\; NeZero\left(n\right) \Rightarrow \left(\forall z \in Fin\left(n\right) \times Sector,\; \forall w \in Fin\left(n\right) \times Sector,\; seam\left(z, w\right) \Leftrightarrow \left(second\left(value\left(second\left(z\right)\right)\right) = 0 \land w = (add\left(first\left(z\right), 1\right), swap\left(second\left(z\right)\right))\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.seam` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The outgoing zero edge (i,a,0) is identified with (i+1,0,a), with positive cyclic wrap.

**Theorem 1.10 (Exact original guarded generators).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall x \in Omega,\; Finite\left(Omega\right) \Rightarrow \left(\forall z \in Fin\left(3 \times pointPeriod\left(u, v, c, x\right)\right) \times Sector,\; \forall w \in Fin\left(3 \times pointPeriod\left(u, v, c, x\right)\right) \times Sector,\; Step\left(u, v, value\left(Phi\left(u, v, c, x, z\right)\right), value\left(Phi\left(u, v, c, x, w\right)\right)\right) \Leftrightarrow \left(seam\left(z, w\right) \lor seam\left(w, z\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actual_step_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every two strict-sector inputs, the original Step between their Phi images holds exactly when one input is a positive seam successor of the other. The omitted-corner guard excludes that face and strict tip positivity excludes the tip face. The two remaining source permutations exchange the incoming and outgoing coordinate roles. Their actual group-action transport and minimal point-period wrap supply the successor and predecessor occurrences.

**Theorem 1.11 (Full original chains and strict fan chains).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall x \in Omega,\; Finite\left(Omega\right) \Rightarrow \left(\forall z \in Fin\left(3 \times pointPeriod\left(u, v, c, x\right)\right) \times Sector,\; \forall w \in Fin\left(3 \times pointPeriod\left(u, v, c, x\right)\right) \times Sector,\; EqvGen\left(Step\left(u, v\right), value\left(Phi\left(u, v, c, x, z\right)\right), value\left(Phi\left(u, v, c, x, w\right)\right)\right) \Leftrightarrow EqvGen\left(seam, z, w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actual_eqvgen_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full original affine EqvGen between two Phi images equals the equivalence generated by the positive strict fan seams. Saturation and reflection in ActualLinkCornerChains retain every intermediate original representative. The constructed bijection transports the restricted chain, and each source generator becomes a seam or its reverse by actual_step_iff. No relation correspondence is a hypothesis.

**Definition 1.12 (Strict sectors in the closed fan carrier).**

$$\forall n \in Nat,\; \forall z \in Fin\left(n\right) \times Sector,\; closedInput\left(z\right) = (first\left(z\right), closedTriangle\left(value\left(second\left(z\right)\right)\right))$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.closedInput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inclusion retains the index and both real coordinates, weakening only the strict radial bound to its non-strict ambient bound.

**Theorem 1.13 (The full original closed-fan equivalence).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall x \in Omega,\; Finite\left(Omega\right) \Rightarrow \left(\forall z \in Fin\left(3 \times pointPeriod\left(u, v, c, x\right)\right) \times Sector,\; \forall w \in Fin\left(3 \times pointPeriod\left(u, v, c, x\right)\right) \times Sector,\; EqvGen\left(Step\left(u, v\right), value\left(Phi\left(u, v, c, x, z\right)\right), value\left(Phi\left(u, v, c, x, w\right)\right)\right) \Leftrightarrow fanRelated\left(closedInput\left(z\right), closedInput\left(w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actual_full_fan_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For strict inputs, the full original affine EqvGen equals the original CyclicTriangleDisk EqvGen after inclusion in its closed carrier. Every closed-fan seam preserves a+b. Equivalence-closure induction therefore keeps every intermediate representative inside the strict cutoff, and reflects the full closed chain to the strict seam chain. The displayed fanRelated denotes the original CyclicTriangleDisk.Related, retaining its generator-defined fan relation.

**Definition 1.14 (The actual strict coordinate equivalence).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall x \in Omega,\; Finite\left(Omega\right) \Rightarrow \left(Equivalence\left(coordinateEquiv\left(u, v, c, x\right), Fin\left(3 \times pointPeriod\left(u, v, c, x\right)\right) \times Sector, Neighborhood\left(u, v, vertex\left(u, v, c, x\right), encode\left(u, v, c, (x, 0)\right)\right)\right) \land forward\left(coordinateEquiv\left(u, v, c, x\right)\right) = Phi\left(u, v, c, x\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.coordinateEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the equivalence determined by the constructed bijection Phi. Its inverse selects the actual occurrence and its two original affine coordinates.

**Definition 1.15 (Original induced coordinate topology).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall x \in Omega,\; Finite\left(Omega\right) \Rightarrow [TopologicalSpace\left(Omega\right)] [DiscreteTopology\left(Omega\right)] Homeomorphism\left(coordinateHomeomorph\left(u, v, c, x\right), Fin\left(3 \times pointPeriod\left(u, v, c, x\right)\right) \times Sector, Neighborhood\left(u, v, vertex\left(u, v, c, x\right), encode\left(u, v, c, (x, 0)\right)\right)\right) \land forward\left(coordinateHomeomorph\left(u, v, c, x\right)\right) = Phi\left(u, v, c, x\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.coordinateHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With discrete Omega, the coordinate equivalence is a homeomorphism for the induced carrier topology. A fiber of the inverse occurrence index fixes the original corner label and imposes a strict dominant-tip inequality, hence is open. The remaining inverse coordinates are twice the incoming and outgoing barycentric entries. This proves both directions of continuity without an assumed homeomorphism.

**Definition 1.16 (The full original affine quotient).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall x \in Omega,\; ActualQuotient\left(u, v, c, x\right) = Quotient\left(Carrier\left(u, v, vertex\left(u, v, c, x\right)\right), EqvGen\left(Step\left(u, v\right)\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.ActualQuotient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The quotient uses the original guarded Step and its full equivalence closure on Carrier at the actual seed vertex. Its topology is the quotient topology of the original carrier.

**Definition 1.17 (Actual quotient neighborhood).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall x \in Omega,\; quotientNeighborhood\left(u, v, c, x\right) = image\left(quotientMk\left(EqvGen\left(Step\left(u, v, vertex\left(u, v, c, x\right)\right)\right)\right), Neighborhood\left(u, v, vertex\left(u, v, c, x\right), encode\left(u, v, c, (x, 0)\right)\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.quotientNeighborhood` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the image of the strict original neighborhood in the full original quotient, carrying its subspace topology. The displayed quotientMk is its canonical quotient projection.

**Theorem 1.18 (Open saturated image and restricted quotient map).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall x \in Omega,\; [TopologicalSpace\left(Omega\right)] [DiscreteTopology\left(Omega\right)] preimage\left(quotientMk\left(EqvGen\left(Step\left(u, v, vertex\left(u, v, c, x\right)\right)\right)\right), quotientNeighborhood\left(u, v, c, x\right)\right) = Neighborhood\left(u, v, vertex\left(u, v, c, x\right), encode\left(u, v, c, (x, 0)\right)\right) \land \left(IsOpen\left(quotientNeighborhood\left(u, v, c, x\right)\right) \land IsQuotientMap\left(restrictPreimage\left(quotientNeighborhood\left(u, v, c, x\right), quotientMk\left(EqvGen\left(Step\left(u, v, vertex\left(u, v, c, x\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actual_open_quotient_neighborhood` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full original chain-saturation theorem gives q inverse of q(N) equal to N. The strict neighborhood N is open: it is a union of strict coordinate inequalities intersected with discrete ordered-corner component conditions. By the quotient topology q(N) is open, and the restriction of q over q(N) is a quotient map. No global openness or Hausdorff property of the actual quotient is assumed.

**Definition 1.19 (Actual strict quotient topology).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall x \in Omega,\; Finite\left(Omega\right) \Rightarrow [TopologicalSpace\left(Omega\right)] [DiscreteTopology\left(Omega\right)] Homeomorphism\left(actualSeamQuotientHomeomorph\left(u, v, c, x\right), Quotient\left(Fin\left(3 \times pointPeriod\left(u, v, c, x\right)\right) \times Sector, EqvGen\left(seam\right)\right), quotientNeighborhood\left(u, v, c, x\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actualSeamQuotientHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The established coordinate homeomorphism and full relation equivalence identify the quotient of strict sectors by the positive seams with the open image in the full original quotient. The restricted actual quotient map supplies exactly its original subspace topology.

**Definition 1.20 (The open unit disk).**

$$\forall z \in Complex,\; member\left(z, OpenDisk\right) \Leftrightarrow norm\left(z\right) < 1$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.OpenDisk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Complex norm strictly less than one, with the induced topology.

**Definition 1.21 (An actual open disk chart).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall x \in Omega,\; Finite\left(Omega\right) \Rightarrow [TopologicalSpace\left(Omega\right)] [DiscreteTopology\left(Omega\right)] Homeomorphism\left(actualOpenDiskChart\left(u, v, c, x\right), quotientNeighborhood\left(u, v, c, x\right), OpenDisk\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actualOpenDiskChart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The chart composes the original strict seam quotient homeomorphism with the restriction of the existing closed radial homeomorphism. The newly public radial_norm is consumed directly; its statement and proof are unchanged. The domain is the open image in the full original quotient and carries its inherited topology.

For the order-halving application, let G and H be finite groups with their canonical regular right multiplication actions and discrete topologies. Fix a homomorphism pi:G -> H and a marked pair u,v in G. Put ell=v inverse times u squared, and assume ell has order four while pi(ell) has order two. Use row zero and root one in the original ordered-endpoint construction. The source neighborhood uses twelve sectors and the corresponding target neighborhood uses six. These orders are hypotheses about the marked return word; no global surjectivity, centrality or kernel-size premise is needed for the following collision argument.

The original carrier map sends ((g,j),beta) to ((pi(g),j),beta), retaining every one of the four real coordinates. Its corner label is transported by the quotient map induced by g -> pi(g). The actual face words commute with pi, so this map preserves each original guarded Step, including its zero-coordinate guard, and therefore the full generated equivalence relation. The induced map F is continuous on the full original link quotient for the selected source corner-vertex label, with values in the quotient for its transported label. These are their original quotient topologies. The source corner-vertex label maps to the target row-zero/root-one corner-vertex label.

In the twelve-sector source neighborhood, compare sector indices zero and six on the two diagonal curves specified below. They have the same phase. Their sheet coordinates are one and ell squared, respectively. For t>0, both triangle coordinates are positive, so the complete original fan correspondence gives distinct cyclic normal forms for these two represented classes inside the strict neighborhood. The actual source classes are therefore different. Their target raw representatives agree: pi(ell squared)=one, and all four coordinates were retained.

For each of these two sectors take a=b=max(0,min(t,1/4)). The resulting curve is continuous for all real t, lies in the strict original neighborhood, equals the literal endpoint at t=0, and has both coordinates positive for every t>0. Any open neighborhood of that endpoint pulls back along both curves to an open neighborhood of zero. Their intersection contains a positive t, giving two distinct points in that same open neighborhood with equal F-images. Thus F is not locally injective at the original endpoint, and cannot be a local homeomorphism or a covering map on the full original link quotient.

This argument establishes collisions arbitrarily close to the specified original endpoint. Exact two-element punctured fibers, a punctured covering theorem, the other endpoint rows, and the ambient three-dimensional retained-tetrahedron map require further arguments. The identification of the full inverse image of the chosen target neighborhood is not established here, and no global kernel size is assumed. The local collision conclusion does not assume those stronger statements.

**Definition 1.22 (The original retained tetrahedron).**

$$\forall a \in Functions\left(Fin\left(4\right), Real\right),\; member\left(a, TruncatedTetrahedron\right) \Leftrightarrow \left(\left(\forall i \in Fin\left(4\right),\; 0 \le eval\left(a, i\right) \land eval\left(a, i\right) \le divide\left(3, 4\right)\right) \land sum\left(a\right) = 1\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.TruncatedTetrahedron` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All four coordinates are between zero and three quarters inclusive, and their sum is one. Every cap and zero-face tie is retained. This is the literal carrier of Original Link Interface section 5.1 with delta=1/4.

**Definition 1.23 (Original tetrahedron copies).**

$$\forall Omega \in Type,\; TruncatedPoint\left(Omega\right) = Omega \times TruncatedTetrahedron$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.TruncatedPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original tetrahedron index in Omega is retained alongside all four affine coordinates.

**Definition 1.24 (The original whole-face transport).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall f \in Fin\left(4\right),\; \forall a \in TruncatedPoint\left(Omega\right),\; first\left(truncatedMove\left(u, v, f, a\right)\right) = act\left(first\left(a\right), faceWord\left(u, v, f\right)\right) \land \left(\forall i \in Fin\left(4\right),\; coordinate\left(truncatedMove\left(u, v, f, a\right), i\right) = coordinate\left(a, inverseApply\left(facePerm\left(f\right), i\right)\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.truncatedMove` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source tetrahedron t moves to act(t,faceWord(u,v,face)); target coordinate i is source coordinate facePerm(f) inverse of i. These are precisely the same original four permutations and words, including both inverse directions.

**Definition 1.25 (The original ambient face guard).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall a \in TruncatedPoint\left(Omega\right),\; \forall b \in TruncatedPoint\left(Omega\right),\; TruncatedStep\left(u, v, a, b\right) \Leftrightarrow \left(\exists f \in Fin\left(4\right),\; coordinate\left(a, f\right) = 0 \land b = truncatedMove\left(u, v, f, a\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.TruncatedStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A generator is allowed exactly when alpha_f=0 and the target is truncatedMove. There is no extra slice or corner guard in the ambient relation.

**Definition 1.26 (The actual labeled cap component).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall a \in TruncatedPoint\left(Omega\right),\; member\left(a, Slice\left(u, v, nu\right)\right) \Leftrightarrow \left(\exists j \in Fin\left(4\right),\; coordinate\left(a, j\right) = divide\left(3, 4\right) \land label\left(pairing\left(u, v\right), (first\left(a\right), j)\right) = nu\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.Slice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A point lies in the slice at nu when some coordinate j equals three quarters and the original corner (t,j) has label nu. Nonnegative coordinates summing to one force this cap index to be unique.

**Definition 1.27 (Literal affine cap coordinates).**

$$\forall j \in Fin\left(4\right),\; \forall b \in Functions\left(Fin\left(4\right), Real\right),\; \forall i \in Fin\left(4\right),\; alpha\left(j, b, i\right) = add\left(if\left(i = j, divide\left(3, 4\right), 0\right), divide\left(eval\left(b, i\right), 4\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.alpha` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map is alpha=(3/4)e_j+(1/4)beta, on the complete original corner triangle beta_j=0, beta nonnegative, sum beta=1.

**Definition 1.28 (The actual affine carrier map).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall p \in Point\left(u, v, nu\right),\; toTruncation\left(u, v, p\right) = (tetrahedron\left(p\right), alpha\left(corner\left(p\right), coordinates\left(p\right)\right))$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.toTruncation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retain t and use alpha at the actual corner j. The original corner label determines the cap component.

**Theorem 1.29 (Full carrier equivalence).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; Bijective\left(codRestrict\left(toTruncation\left(u, v\right), Slice\left(u, v, nu\right)\right), Point\left(u, v, nu\right), Slice\left(u, v, nu\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actual_slice_carriers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map into Slice is bijective. The inverse recovers the unique cap index j and sets beta_j=0 and beta_i=4 alpha_i for i different from j. The complete carrier includes all boundary ties, with no strict cutoff imposed on this comparison.

**Theorem 1.30 (Exact slice generators).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall p \in Point\left(u, v, nu\right),\; \forall q \in Point\left(u, v, nu\right),\; Step\left(u, v, p, q\right) \Leftrightarrow TruncatedStep\left(u, v, toTruncation\left(u, v, p\right), toTruncation\left(u, v, q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actual_slice_step_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original Step holds if and only if ambient TruncatedStep holds between the affine images. The positive cap coordinate excludes the omitted corner face automatically. For every other face alpha_f=0 is equivalent to beta_f=0. Alpha commutes with the actual coordinate permutation, and pairedPoint preserves the original corner label.

**Theorem 1.31 (Full ambient chain reflection).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall p \in Point\left(u, v, nu\right),\; \forall q \in Point\left(u, v, nu\right),\; EqvGen\left(Step\left(u, v\right), p, q\right) \Leftrightarrow EqvGen\left(TruncatedStep\left(u, v\right), toTruncation\left(u, v, p\right), toTruncation\left(u, v, q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actual_slice_eqvgen_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equivalence holds for the full original ambient EqvGen, not merely for chains assumed to stay in the slice. Each ambient generator preserves slice membership in both directions. In the backward direction its cap coordinate is pulled through the inverse permutation; the original pairedPoint construction transports the label, and uniqueness of the cap index recovers the specified label. EqvGen induction then retains every transitive intermediate before transporting the chain through the carrier bijection.

**Definition 1.32 (Actual carrier topology).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; Finite\left(Omega\right) \Rightarrow [TopologicalSpace\left(Omega\right)] [DiscreteTopology\left(Omega\right)] Homeomorphism\left(actualSliceHomeomorph\left(u, v, nu\right), Point\left(u, v, nu\right), Slice\left(u, v, nu\right)\right) \land forward\left(actualSliceHomeomorph\left(u, v, nu\right)\right) = codRestrict\left(toTruncation\left(u, v\right), Slice\left(u, v, nu\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actualSliceHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With finite discrete Omega, the original full corner carrier is compact and the original cap subspace is Hausdorff. The literal affine carrier bijection is continuous, hence a homeomorphism. Both topologies are inherited from the actual labels and real coordinate arrays.

**Definition 1.33 (The full original truncated quotient).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; TruncatedQuotient\left(u, v, Omega\right) = Quotient\left(TruncatedPoint\left(Omega\right), EqvGen\left(TruncatedStep\left(u, v\right)\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.TruncatedQuotient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The quotient is generated by TruncatedStep on all original retained tetrahedra, with its quotient topology.

**Definition 1.34 (The original cap image).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; quotientSlice\left(u, v, nu\right) = image\left(truncatedQuotientMk\left(u, v\right), Slice\left(u, v, nu\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.quotientSlice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the image of Slice under the full ambient quotient projection, with its inherited topology.

**Definition 1.35 (The full original quotient comparison).**

$$\forall G \in Type,\; \forall Omega \in Type,\; [Group\left(G\right)] [MulAction\left(Opposite\left(G\right), Omega\right)] \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; Finite\left(Omega\right) \Rightarrow [TopologicalSpace\left(Omega\right)] [DiscreteTopology\left(Omega\right)] Homeomorphism\left(actualSliceQuotientHomeomorph\left(u, v, nu\right), Quotient\left(Point\left(u, v, nu\right), EqvGen\left(Step\left(u, v\right)\right)\right), quotientSlice\left(u, v, nu\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actualSliceQuotientHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Full-chain invariance proves that the inverse image of the cap image is exactly Slice. Slice is a finite union of closed cap-coordinate and discrete-label conditions, so its quotient image is closed. The closed-subspace quotient criterion supplies the restricted quotient map. Composing it with the actual carrier homeomorphism and exact full relation theorem yields the displayed homeomorphism. No quotient correspondence or slice invariance is an assumption. This does not identify the retained quotient with the separately specified marked manifold in main theory 70.10.

Application: the cap comparison for an arbitrary original face pairing. Let T be any tetrahedron index type and let P be EdgeStarTransitions.RawFacePairing T, with its given facePair and three-edge-slot permutations faceMap. Retain P's fixed-point-free involutive whole-face pairing and its inverse compatibility for the slot maps. The following construction uses this same P throughout; it requires neither a group action nor a presentation by two fixed face words. Its carrier bijection, generator correspondence and full-chain statements do not require T to be finite. Finiteness and the discrete topology on T enter the homeomorphism argument below.

The four-vertex transport is determined by the original edge slots. For a face f, let chi_f be the identity on Fin 3 if f=0 and the exchange of slots 0 and 2 otherwise. Let b_f:Fin 4 -> Option(Fin 3) send f to none and the vertex in increasing face-vertex slot r to some(chi_f(r)). Thus b_f inverse at some(n) is the vertex opposite original face-edge slot n. If x=(t,f) and P.facePair(x)=(t',f'), define sigma_x=b_f' inverse composed with Option.map(P.faceMap(x)) composed with b_f. It sends f to f', transports the opposite vertex of slot n to that of slot P.faceMap(x)(n), and carries precisely the two endpoints of each original face edge to those of its paired edge. The inverse compatibility in P gives sigma_(P.facePair(x))=sigma_x inverse; no independent four-vertex permutation is assumed.

To use the existing generic corner supplier, define q:ActualCornerTransport.Pairing T with q.p=P.facePair and increasing-slot map q.sigma(x)(r)=chi_f'(P.faceMap(x)(chi_f(r))). The involutivity of chi and P's inverse law prove q's compatibility. In these coordinates the supplier's edgeRel(q,i,j) is equivalent, generator for generator, to P.edgeStep(i,j) on the same T times Fin 6. There is no replacement face table or independently chosen edge-label map. Use the existing ActualCornerTransport.Vertex(q) and label(q,(t,j)) for the corner classes, and fix nu in that quotient. This retains the corner relation generated by the same actual face pairing.

The complete corner carrier at nu consists of ((t,j),beta) with beta_j=0, all beta_i>=0, sum_i beta_i=1 and label(q,(t,j))=nu. Its guarded face step chooses f different from j with beta_f=0, moves t to the tetrahedron component of P.facePair(t,f), moves j to sigma_(t,f)(j), and sends each target coordinate i to beta_(sigma_(t,f) inverse(i)). The corner supplier's generator transports the label, so this is a step in the same nu carrier. On the retained tetrahedra use exactly the existing four-coordinate carrier 0<=alpha_i<=3/4, sum_i alpha_i=1. Its ambient face step has only the guard alpha_f=0 and uses that same P.facePair(t,f) and sigma_(t,f) on all four coordinates.

For this P, let S_nu consist of retained points (t,alpha) with alpha_j=3/4 and label(q,(t,j))=nu for some j. Nonnegativity and the sum-one equation make j unique. The literal affine map alpha=(3/4)e_j+(1/4)beta retains t and bijects the full corner carrier with S_nu. Its inverse uses the unique cap index, sets beta_j=0 and beta_i=4*alpha_i for i different from j. All zero-coordinate ties and triangle-boundary points are included. The positive cap coordinate excludes f=j from any ambient face step, while for f different from j the equations alpha_f=0 and beta_f=0 are equivalent. Permuting the original coordinates commutes with this affine formula, giving the exact two-way generator correspondence.

This comparison uses the full ambient equivalence closure. Every ambient face generator preserves membership in S_nu in both directions: the cap index is moved by sigma, or recovered by its inverse, and the same corner transport preserves its label. Induction through reflexivity, reversal and transitivity therefore keeps every intermediate representative of an ambient chain in S_nu. Consequently two complete corner representatives are related by the full guarded corner EqvGen exactly when their affine images are related by the full ambient truncated-face EqvGen. If Q is the quotient projection from all retained tetrahedra by that ambient relation, this also proves Q inverse(Q(S_nu))=S_nu. No restriction on the intermediate chain or separate saturation hypothesis is supplied.

Now assume T is finite and carries the discrete topology. Give the corner carrier and S_nu their actual subspace topologies from the original finite labels and real coordinate arrays. The corner carrier is closed and compact, the affine map is continuous, and the target cap subspace is Hausdorff, so the established carrier bijection is a homeomorphism. S_nu is a finite union, over its cap index, of closed cap-coordinate and discrete-label conditions. Its saturation and the quotient topology of Q imply that Q(S_nu) is closed and that Q restricted over this image is a quotient map. This does not require the full ambient quotient to be Hausdorff or Q to be a closed map on arbitrary subsets. Composing this restricted quotient map with the carrier homeomorphism and the exact full-relation correspondence gives a homeomorphism from the quotient of the complete nu corner carrier by its guarded EqvGen onto Q(S_nu) with the topology inherited from the full ambient retained quotient.

This arbitrary-P comparison keeps the original finite table available without identifying it with the fixed Link(u,v) construction. In particular it supplies no identification of that fixed construction with the separately specified eighteen- and six-triangle corner fibers of the original six-tetrahedron table. Such component identifications and their marked incidences require their own actual-table arguments. The cap comparison alone supplies neither an edge-fan enumeration nor cyclic disk charts, a three-dimensional atlas or a manifold theorem; it also makes no orientability, genus, metric or marked-manifold identification. The earlier fixed-word disk-chart conclusions retain their original group-action and occurrence hypotheses.

Application: strict representative coordinates for an arbitrary original face pairing. Retain the same RawFacePairing P on any tetrahedron type T, its derived four-vertex permutation sigma, its original corner quotient and its guarded barycentric Point carrier. Write d0=((t0,j0),k0) with j0 different from k0, and let nu be the original corner label of (t0,j0). Let D consist of every unequal ordered dart d in the full original DartRelated component of d0. No finite-T, coloring, group-action or local no-edge-reversal premise is needed for the representative-coordinate construction below.

The original strict neighborhood N consists of all Point representatives ((t,j),b) at nu for which some k satisfies b_k>1/2 and DartRelated(P,d0,((t,j),k)). Here b_j=0, all four b coordinates are nonnegative, and their sum is one. The corner and the dominant tip remain ordered. The simplex equation makes the coordinate greater than one half unique; the strict bound excludes the cutoff boundary but retains both seam axes and the endpoint apex.

This N is saturated for the full original Point equivalence relation. Across an actual Step at face f, the original guard gives f different from j and b_f=0. A strict dominant coordinate b_k>1/2 forces f different from k, so the very same face crossing is an original DartStep on ((t,j),k). Sigma transports the dominant tip and all barycentric entries. The paired inverse gives the converse step, and induction through the full EqvGen gives membership in N in both directions for every ambient intermediate. Consequently the full ambient Point relation between members of N is exactly the equivalence closure of its original Step restricted to N, rather than a relation defined by excluding ambient intermediates.

Choose any function r from the original occurrences T times Fin(6) to Bool. For d=((t,j),k) in D, its original edge is e=edgeIndex(j,k). If r(t,e) is false, take I to be the first face of edgeFaces(e) and O the second; if it is true, exchange these roles. The actual six-edge table makes j,k,O,I four distinct elements of Fin(4). The resulting permutation F_d sends 0 to j, 1 to k, 2 to O and 3 to I. This is only a local coordinate ordering. No compatibility of r across paired faces, global edge orientation or cyclic successor is assumed for these coordinates.

Use the existing strict sector S={(a,b):a>=0,b>=0,a+b<1}. Pull the canonical beta coordinates for row zero and phase zero back by F_d inverse. In the actual original positions the resulting array B has B_j=0, B_k=1-(a+b)/2, B_I=a/2 and B_O=b/2. Permutation invariance of the finite sum transfers the canonical simplex bounds: every B coordinate is nonnegative, their sum is one, and B_k>1/2. Thus the construction retains all four original positions instead of replacing them by a new face table.

Define Phi:D times S -> N by Phi(d,(a,b))=((t,j),B). The full original dart-chain invariant preserves the corner label nu, so this is a map to the same Point carrier and N, with the displayed original representative as its value. Every strict representative y in N supplies its unique dominant tip k and therefore the actual dart d=((t,j),k) in D. Its inverse sector coordinates are a=2b_I and b=2b_O. Applying the canonical inverse-sector identity after the same permutation proves nonnegativity, a+b<1 and recovery of all four entries. This proves surjectivity without an assumed enumeration of D.

The map is also injective. Equality of represented raw points first gives equality of their original corners. Dominant-coordinate uniqueness identifies their tips, hence their actual ordered darts and their elements of D. Evaluation at the same I and O then identifies both sector coordinates. Thus Phi is a bijection on the entire original component times S, including the two axes and the apex, repeated incidence labels and arbitrary paired ports. It does not require D to be finite or identify ordered darts with unoriented occurrences.

For the topological conclusion, give T a discrete topology and retain the induced topologies on the original ordered-dart carrier, its unequal-dart subtype, D and N. The topology on D is exactly this nested subtype topology; its discreteness is a consequence of the discrete original labels, not a replacement choice of topology. For a fixed d the forward coordinates are affine in the two real sector coordinates, and continuity on the discrete product proves continuity of Phi.

The inverse component fiber at d is precisely the intersection of the original corner equality y.corner=d.corner with the strict inequality y.b(d.tip)>1/2. Both sets are open in the original subspace topology, so the recovered D coordinate is continuous. The two remaining inverse coordinates evaluate the original barycentric array at the recovered incoming and outgoing faces and multiply by two. Coordinate evaluation with a discrete index is continuous. The established bijection therefore gives a homeomorphism D times S with N for their original induced topologies, still without a finite-T or local no-edge-reversal premise.

The image U of N in the full original Point quotient is open, and the original projection restricted over U is a quotient map. Indeed N is a union over the four possible tips of a strict coordinate inequality intersected with a discrete original-component condition, so N is open. Its full-chain saturation gives q inverse(U)=N. The quotient topology then gives openness of U and the usual open-subspace restriction gives the stated quotient map. No global openness of q, separation property of the ambient quotient or finite-type compactness argument is assumed.

These applications establish the original representative-coordinate homeomorphism and the open saturated quotient neighborhood. They do not yet identify the equivalence relation on D times S with cyclic seams or identify U with a disk. Actual successor transport, the complete Step-to-seam comparison, full-chain quotient transport and any finite ordered-cycle hypotheses must be supplied separately. No eighteen- or six-element fixture, atlas, marked-manifold, orientability or geometric-realization conclusion is inferred. The earlier fixed-word disk theorems keep their original hypotheses. This application introduces no mathematical declaration or theorem Describe and makes no literature-priority claim.

Application: actual cyclic seams for the same original face pairing. Now assume T is finite and keep an unequal root dart d0 whose full original DartRelated component does not contain its endpoint-swapped dart. This is a root-local no-edge-reversal hypothesis; it is not inferred from arbitrary P. Use a coloring-free occurrence orientation s supplied by the original finite pairing construction, and use its same incoming and outgoing face choices throughout the affine coordinates and the successor.

Let m be the cardinality of the entire original edgeLabel fiber through d0. The established occurrence cycle and the root-local condition give an enumeration E:Fin(m) -> D of the full original ordered component. Its next dart is exactly the original outgoing-face DartMove, and E(i+1) is this next dart, with addition in Fin(m). Thus m counts original unoriented occurrences rather than the two ports at every occurrence. Only positivity of m is used; singleton and two-element cycles, loops and repeated ports remain in scope.

At d=E(i), keep the original four positions j,k,I,O and the same array B_j=0, B_k=1-(a+b)/2, B_I=a/2 and B_O=b/2. For the original outgoing face crossing, the actual sigma sends j to the next corner, k to the next tip, O to the next incoming face and I to the next outgoing face. Evaluating all four positions therefore gives move_O(B(d,(a,b)))=B(E(i+1),(b,a)) as an equality of original raw arrays. This affine equality by itself does not assert that the outgoing face has zero coordinate.

The incoming crossing is recovered from that same original face pairing. Apply the outgoing equality at the actual predecessor to the swapped sector coordinate, use the actual paired target face as the current incoming face, and then use the original move-inverse law. This gives move_I(B(E(i),(a,b)))=B(E(i-1),(b,a)). The predecessor and successor retain the cyclic wrap in Fin(m); no independently chosen inverse transport or replacement face table is assumed.

Composing E times the identity on the strict sector with the full representative-coordinate bijection gives an indexed bijection Phi:Fin(m) times S -> N with its original Point representative as its value. The finite index is tied to the actual original dart E(i). No equality of raw coordinates, quotient relation or chart is inserted as a hypothesis of this bijection.

The complete guarded original Step between Phi(z) and Phi(w) holds exactly when z is a positive cyclic seam predecessor of w or w is a positive cyclic seam predecessor of z. Indeed the original guard excludes the omitted corner face, and the coordinate at the tip is greater than one half, excluding the tip face. The only possible faces are the actual O and I. Their zero guards are respectively b=0 and a=0, and the two established affine transport equalities give precisely (i,a,0) -> (i+1,0,a) and its reverse. Injectivity of Phi proves the converse identification of the complete target representative.

This generator equivalence includes both axes and the apex. It does not assume that a point has a unique legal face crossing: at the apex both seam guards may hold, and small cyclic indices may identify a successor with a predecessor. The exact disjunction and the full closure retain these cases without deleting representatives or requiring m to be at least three.

Finally, full-chain saturation and reflection of the original strict neighborhood retain every intermediate Point representative of an ambient chain. Transporting that restricted chain through the indexed bijection turns every generator into a seam or its reverse. Conversely every positive seam gives a legal original guarded Step. Thus the full original Related(P,Phi(z),Phi(w)) is equivalent to EqvGen of the canonical positive seam on Fin(m) times S. This establishes the relation comparison; descending it with the inherited quotient topology and obtaining a disk chart require the further topological construction.

The same finite-P construction also has the full closed-fan relation comparison. Include each strict sector in the existing closed triangle carrier, keeping its cyclic index and both coordinates. Every closed-fan generator preserves a+b, so the existing closed-chain restriction reflects every full closed-fan chain between strict inputs back to the strict seam relation. Composing that restriction with the original Related-to-seam equivalence gives exactly the original CyclicTriangleDisk.Related on the included representatives, including all ambient closed-fan intermediates.

For the chart, assume in addition that T has its given discrete topology. Give the original ordered component D exactly the nested induced topology used above. The finite enumeration E:Fin(m) -> D and its inverse are continuous because these original label spaces are discrete. Taking its product with the identity on S and composing with the established D times S coordinate homeomorphism gives an indexed coordinate homeomorphism Fin(m) times S with the same original strict neighborhood N. Its underlying map is exactly Phi; the topology on D or N is not replaced.

Let q be the full original Point quotient projection, and let U=q(N) carry its inherited subspace topology. The established full-chain saturation gives q inverse(U)=N, and U is open. Identify N with that inverse-image subspace and compose the indexed coordinate homeomorphism with the actual restriction of q over U. The resulting map f:Fin(m) times S -> U is a quotient map by composition of the two homeomorphisms with the original restricted quotient map.

The kernel relation of this same f is exactly EqvGen of the positive cyclic seam. In one direction the full original Related-to-seam comparison and Quotient.sound give equal original quotient images. In the other direction equality in the actual subspace U gives equality of the original ambient quotient values; Quotient.exact recovers the full original Related, and the checked relation comparison recovers the seam closure. The standard quotient-map homeomorphism therefore identifies the strict seam quotient with U in precisely its inherited original topology. No independent quotient relation or quotient-topology correspondence is a hypothesis.

Finally compose the inverse of this strict seam quotient homeomorphism with the existing strictFanDiskHomeomorph. This gives a homeomorphism from U onto the open complex unit disk. The reused disk supplier restricts the existing closed radial homeomorphism using its original radial norm identity; it applies to every positive m and imposes no lower bound of three. The chart thus retains singleton and two-element cycles, axes and apex, as well as the original repeated ports, under the explicit root-local no-edge-reversal condition.

This disk chart concerns the open strict neighborhood in the full original corner Point quotient of the same P. Its assumptions are finite tetrahedron indices with discrete topology, the constructed occurrence orientation and the stated local no-edge-reversal condition. Combining it with the separate full cap-quotient homeomorphism requires transporting the actual neighborhood and its topology through that comparison. The result here identifies neither the eighteen- and six-triangle fixtures nor a three-dimensional atlas, an orientability or genus statement, the separately marked manifold or a geometric realization. All displayed applications reuse existing mathematical suppliers and introduce no mathematical declaration, theorem Describe or literature-priority claim.

The chart transports to the actual labeled cap image through the earlier full cap-quotient comparison. Let e be that homeomorphism from the full original corner Point quotient at nu to Q(S_nu), the cap image in the full retained-tetrahedron quotient. For every original corner representative p, the value of e at its quotient class is the original ambient retained quotient class of the literal affine point (3/4)e_j+(1/4)beta. This representative identity ties the comparison to the same original P and coordinates.

Define V=e(U) as a subset of Q(S_nu). Equivalently, its members are exactly the original retained quotient classes of those literal affine images whose corner representatives lie in the full strict neighborhood N. Since U is open and e is a homeomorphism, V is open relative to the actual cap image with its inherited topology. This is a relative openness statement on the cap surface; it does not assert that V is open in the full three-dimensional retained quotient.

The homeomorphism from U to V obtained by restricting e has the same original values. Compose its inverse with the constructed U-to-open-disk chart to obtain a disk chart on V. This retains the same finite P, discrete original topology and explicit root-local no-edge-reversal condition, including m=1 and m=2 and all original axes, apex and repeated ports. The transported chart supplies a neighborhood on the actual labeled cap image, without identifying the original eighteen- and six-triangle fixtures, constructing a three-dimensional atlas, classifying the cap component or establishing a marked-manifold or geometric-realization theorem.

Application: the literal six-tetrahedron pairing. Take T=Fin(6). Pair the faces (0,0)-(2,0), (0,1)-(1,2), (0,2)-(1,0), (0,3)-(2,3), (1,1)-(2,2), (1,3)-(4,3), (2,1)-(3,2), (3,0)-(5,0), (3,1)-(4,2), (3,3)-(5,3), (4,0)-(5,1) and (4,1)-(5,2). These twelve pairs cover all twenty-four directed faces. Use the four-position image tuple (0,2,1,3) on each listed pair except (0,2)-(1,0), which uses (2,1,0,3), and the three pairs (0,3)-(2,3), (3,3)-(5,3), (4,0)-(5,1), which use (1,0,2,3). Reverse directions use the inverse permutation, equal to the same transposition in each case.

Let P be this literal RawFacePairing, with its face maps expressed in the original faceEdge slot convention. The four-position sigma derived from those actual three-slot maps agrees with every listed vertex permutation in both directions. Thus the corner pairing used in the original Vertex quotient is the same face pairing at every original tetrahedron and vertex; no group-action pairing or equally sized replacement carrier is substituted.

Every original corner (t,v) is related through actual face-corner slots to (0,0) when v is not 3, and to (0,3) when v is 3. Conversely every original corner generator preserves whether v=3, and this property is preserved by the full generated relation. Consequently label(P,(t,v))=label(P,(u,w)) holds exactly when either both vertex values equal 3 or both differ from 3. The two displayed labels are distinct and exhaust the original Vertex quotient.

The entire original label fiber through (0,0) is therefore in bijection with Fin(6) times Fin(3), by retaining t and the original vertex value v<3; its inverse retains t and includes that value in Fin(4). The entire original fiber through (0,3) is in bijection with Fin(6), by retaining t, with inverse t mapped to (t,3). Their cardinalities are eighteen and six. These are the full index sets of the original corner triangles, with their actual corner representatives retained.

In local edge order (01,02,03,23,13,12), designate endpoints by the six rows (0,0,0,2,1,2), (0,2,0,2,1,2), (1,2,0,2,1,1), (1,2,0,2,1,1), (1,0,0,2,1,1), (0,0,0,2,1,2). Each entry is one of the two original endpoints of that local edge. For an unequal ordered dart, give value true exactly when its first endpoint is the designated endpoint at its original occurrence. Give diagonal darts value false only to make this Boolean label total.

Every legal original DartMove preserves this Boolean label, including both incident face choices of every unequal dart. Endpoint swap negates it on every unequal dart. Propagating equality through all constructors of the full original DartRelated relation therefore rules out a path from any unequal root to its swapped root. Thus this same P satisfies the root-local no-edge-reversal condition at every original ordered root, without assuming a finite bound on paths or identifying equal Boolean values with connected components.

Give Fin(6) its discrete topology and use the coloring-free occurrence orientation of this same P. For each unequal original root, the preceding actual-cap disk construction now applies with its local no-edge-reversal premise discharged by the designated-endpoint invariant. It gives a disk chart on the same capStrictImage, whose points are exactly the retained quotient classes of the literal affine cap images of strict original corner representatives. The domain is open relative to the actual labeled cap image; its cyclic index is still the whole original edge-occurrence fiber.

By themselves, the two corner-fiber identifications and the strict local cap charts do not classify the complete cap components as surfaces or supply a complete atlas. The global edge classification and further chart constructions have their own arguments below. Orientability, genus, comparison with the separately marked three-dimensional manifold and physical geometric realization require their respective additional arguments.

The same literal pairing also determines the complete original global-edge quotient. In local edge order (01,02,03,23,13,12), label the six tetrahedron rows by (A,B,C,C,C,B), (B,A,C,C,C,A), (A,B,C,C,C,B), (B,A,C,C,C,A), (A,B,C,C,C,A) and (B,A,C,C,C,A). The labels A, B and C denote the original edgeLabel classes through occurrences (0,0), (0,1) and (0,2), respectively; the local edge index remains the original one.

Every original occurrence has an actual face-edge-slot path to the representative prescribed by this table. Conversely every original face-edge generator preserves its table label, and the label is preserved by all constructors of the full generated equivalence relation. Thus two original occurrences have the same edgeLabel exactly when their table labels agree. The path witnesses establish the forward connections, while the preserved label rules out any additional connections through arbitrarily long generated chains.

The resulting map from the original GlobalEdge quotient to {A,B,C} is a bijection and sends every original edgeLabel to its stated table value. Its inverse uses the three original representative labels, so the three classes are distinct and exhaust the whole original quotient. The quotient here is generated by the actual paired face-edge slots of this P, with no prior independently assigned global-edge carrier.

For each representative, the entire original edgeLabel fiber is in bijection with the subtype of the same original occurrences having its table value; the map and inverse retain the occurrence itself. These three full fibers have cardinalities ten, eight and eighteen. For an arbitrary original occurrence, its full edgeLabel fiber has the corresponding one of these cardinalities, so every actual global-edge degree is at least six. Each count records local edge occurrences once, rather than counting their two endpoint lifts or their two incident face ports.

For an arbitrary finite tetrahedron type with its discrete topology and the same raw face-pairing data, the complete original retained-carrier relation is closed in the square of that carrier. The retained coordinates still satisfy all four bounds from zero to three quarters and have sum one; the relation is generated by the actual coordinate-zero face moves and all their finite chains. The closedness statement concerns the full retained carrier, including points outside the cap slices. The full original retained quotient is compact and Hausdorff. Compactness of the retained carrier and its quotient uses only finiteness of the tetrahedron type; discreteness supplies the separation argument.

For every original vertex label, its actual cap image is a closed subspace of that same full quotient and is therefore compact and Hausdorff. The established homeomorphism from the complete original corner quotient to this inherited cap subspace also gives Hausdorffness of the corner quotient. These statements retain the actual labeled slice, its saturation under the full original relation, and the quotient and subspace topologies. They do not require a nonempty label fiber, a chosen cap point, an occurrence orientation or local no-edge-reversal.

The remaining local analysis retains the same original guarded relation for arbitrary tetrahedron types, without finiteness or a supplied topology. An original corner representative whose three coordinates away from its omitted corner are all nonzero has a singleton class under the full generated relation. If exactly one of those three coordinates vanishes, at an original face f, its class consists exactly of itself and its actual paired representative across f. Those two representatives are distinct by fixed-freeness of the original face pairing, including when the paired faces lie in the same tetrahedron. The proof transports the unique vanishing side across every legal move and handles every constructor of the generated relation, so it does not bound the length of an ambient chain.

These separation, compactness and representative-class results provide prerequisites for the triangle-interior and edge-interior charts. The strict tip charts cover their stated dominant-coordinate neighborhoods. A complete atlas requires chart constructions and a coverage argument; surface classification and the later three-dimensional manifold comparison require further conclusions.

For discrete tetrahedron indices, fix an original corner c=(t,j) whose label is nu. The complete strict interior of that original corner triangle consists of the original Point representatives with corner c and all three non-omitted coordinates nonzero. This representative patch is open and saturated under the full original guarded relation. Its image is open in the full original corner quotient, and the original quotient projection restricts to a homeomorphism onto that image. These statements use neither finite tetrahedron indices nor a no-edge-reversal hypothesis.

Use the original faceVertex(j,0), faceVertex(j,1) and faceVertex(j,2) order on the three vertices other than j. The plane domain is u>0, v>0 and u+v<1. Send (u,v) to the original corner representative with omitted coordinate j equal to zero and the other three coordinates equal to u, v and 1-u-v in that order. The inverse reads the first two of those same original coordinates. The sum-one identity reconstructs the third coordinate, and coordinate continuity gives a homeomorphism from this open subset of the real plane onto the original strict-interior representative patch. Composing with the restricted original quotient projection yields a chart onto its open quotient image.

When the same tetrahedron type is finite, transport this chart through the established original corner-to-cap quotient homeomorphism. Its image in the actual labeled cap is exactly the retained quotient classes of the literal affine cap representatives from this original strict-interior patch. The transported image is open relative to that actual cap subspace with its inherited topology, and the same open plane triangle is homeomorphic to it. This transports the original points and relation; it assumes neither an independent comparison space nor openness in the full three-dimensional retained quotient.

These plane-triangle charts cover the complete triangle-interior parts. The strict tip charts retain their earlier finite, discrete and local no-edge-reversal hypotheses and cover their stated dominant-coordinate neighborhoods. The edge-interior case uses the following double-band construction. A complete atlas also requires a coverage argument for the chart types.

For an arbitrary raw face pairing, fix an original corner (t,e(0)) with label nu, where e is a permutation of the four original vertex indices, and let the crossing face be e(2). Choose real parameters a,b,d with a>0, d>0, b+d<1, d<=a and b+2d<=1. In this frame the half-band a<u<b, 0<=v<d maps to the original corner representative with coordinates (0,u,v,1-u-v). Reading the coordinates at e(1) and e(2) gives its inverse. With discrete tetrahedron indices this is an open embedding into the original corner carrier.

The partner corner and partner frame are obtained from the actual face pair at (t,e(2)) and its four-index permutation; its label is derived from that same pairing. The parameter point in the partner band is exactly the original paired representative. The two bands have disjoint original images even for same-tetrahedron or same-corner face identifications: fixed-freeness excludes the crossing face, and the two separation bounds exclude the other possible face coordinates. Under the full original generated relation, points on the same band are equivalent exactly when their parameters agree, while opposite-band points are equivalent exactly when their parameters agree and v=0. The union of the two actual band images is saturated in the entire original corner carrier, including under chains with arbitrary intermediate representatives.

Form the doubled closed upper half-plane by identifying its two copies only along their common height-zero boundary. The signed map sends (u,v) on the first copy to (u,v) and on the second to (u,-v). Its fibers are exactly the full generated boundary relation, and it is a continuous closed surjection onto the real plane. The two model bands form the complete inverse image of the open rectangle a<u<b, -d<v<d. Restricting this quotient map to that open rectangle and using the established full original relation correspondence gives a homeomorphism from the actual original double-band quotient image onto the rectangle. The image is open in the original corner quotient; both directions use its original quotient topology.

Every original edge-interior representative belongs to one of these neighborhoods. Choose e(0) to be its omitted corner and e(2) its unique vanishing non-omitted coordinate. Its coordinate u at e(1) satisfies 0<u<1. The choices a=u/2, b=(1+u)/2 and d=min(u,1-u)/8 satisfy all the band bounds, with d>0 and a<u<b; the original representative is the parameter point (u,0). Consequently every such original quotient class has an open neighborhood homeomorphic to an open rectangle in the real plane. This uses discrete tetrahedron indices, with no finiteness, no-edge-reversal or no-self-pairing assumption.

For finite discrete tetrahedron indices, transport each edge-interior neighborhood through the established original corner-to-cap quotient homeomorphism. The transported point is exactly the retained quotient class of its literal affine cap representative, and the transported neighborhood is open relative to the same actual labeled cap subspace. Thus all original edge-interior classes have plane charts in that actual cap. The following common coverage argument combines these edge-interior charts with the preceding interior and strict tip charts. Orientability, genus, the separately marked three-dimensional manifold comparison and physical realization require further arguments.

The chart types cover every original corner representative for finite discrete tetrahedron indices when no-edge-reversal holds at every original ordered root. First use the plane-triangle chart when all non-omitted coordinates are nonzero. Otherwise choose a vanishing non-omitted coordinate and use the edge chart if it is the only such zero. In the remaining case there are at least two vanishing non-omitted coordinates; together with the omitted zero, the sum-one identity makes the last coordinate equal to one. It therefore lies in a strict dominant-coordinate neighborhood. These cases are selected in that order; the chart domains themselves may overlap.

For a dominant coordinate k at the original corner c, take the actual ordered root (c,k). The omitted-zero condition ensures that its endpoints are unequal. The original representative lies in that root's strict neighborhood by the reflexive original dart path, and the root-local no-edge-reversal premise supplies its established disk chart. The complex open unit disk is carried to an open subset of the real plane by the standard real-and-imaginary-coordinate homeomorphism. Applying this argument to every representative gives a plane chart through every point of the full original corner quotient. The original corner-to-cap quotient homeomorphism transports this complete cover to every point of the same actual labeled cap, with its inherited topology.

Each local homeomorphism between open subspaces extends to an open partial homeomorphism on the ambient cap, with the chosen point in its source. Choosing one such chart at each point equips the original cap topology with a standard real-plane charted-space structure. The cap is already compact and Hausdorff. Compactness supplies sigma-compactness, and a charted space over the second-countable real plane is second countable when it is sigma-compact. Thus the actual labeled cap is a compact Hausdorff second-countable topological two-dimensional manifold without boundary. This statement allows disconnected spaces and, for an absent label fiber, the empty space; it asserts no differentiable structure.

For an arbitrary topology on the original tetrahedron type, fix an original raw face pairing and an original vertex label. RawFaceLinkPathConnected.original_quotient_path_connected gives path connectedness of the complete original barycentric corner quotient. It lifts an original corner-label chain through actual points of its triangles: unit-coordinate points supply crossing faces, convexity joins points in one fixed triangle, and the original quotient identifications concatenate these paths. In a transitive chain the same constructed middle point is used on both sides. This result requires neither finiteness nor discreteness of the tetrahedron type and retains its given product, subtype and quotient topologies.

For finite discrete tetrahedron indices, the established original corner-to-cap quotient homeomorphism transports this path connectedness to the same actual labeled cap with its inherited topology. Combining it with the complete plane-chart construction under no-edge-reversal at every original ordered root gives a connected compact Hausdorff second-countable topological surface without boundary. The path-connectedness argument itself uses no no-edge-reversal premise; that premise supplies the dominant-coordinate charts in the surface argument.

For the same literal six-tetrahedron pairing, the previously established original endpoint invariant discharges local no-edge-reversal at every ordered root. The complete chart cover and standard surface structure therefore apply to every original vertex label, including the two labels represented by (0,0) and (0,3). Their original corner fibers still have eighteen and six members, respectively. These results establish connected compact topological surfaces for both actual cap spaces. Orientability, genus, a separately marked three-dimensional manifold identification and physical geometric realization require further arguments.

Application: an actual collar of each original cap. Let T be finite with its given discrete topology, and let P be an arbitrary original RawFacePairing. Use the same retained tetrahedra: the four coordinates are nonnegative, sum to one and are each at most three quarters. Let Q be their full quotient by the equivalence generated by actual zero-coordinate face moves, using the vertex permutations derived from the original faceEdge maps. For an original vertex label nu, retain the actual cap image Cap(nu) in Q with its inherited topology.

Let D(nu) consist of original retained representatives with a coordinate x_j greater than one half and original corner label label(P,(t,j))=nu. That index j is unique by nonnegativity and the sum-one equation. Set U(nu)=q(D(nu)) in the same full Q. An original corner representative p with omitted coordinate p_j=0, nonnegative coordinates summing to one and label nu, together with 0<=h<1/4, maps to x_j=3/4-h and x_i=(1/4+h)p_i for i different from j. The inverse reads j, sets h=3/4-x_j and normalizes p_i=x_i/(1-x_j) off j, with p_j=0. The retained coordinate bound gives 0<=h, and the strict dominant inequality gives h<1/4. The denominator is at least one quarter. All corner edges, vertices and zero-coordinate ties are retained. The excluded height h=1/4 would allow two coordinates equal to one half and is outside this collar.

Every legal original zero-coordinate move preserves the dominant value and transports its index by the derived original vertex permutation. It therefore preserves h and the original label. Conversely the affine formula transports each guarded original corner move to exactly that retained face move. Saturation extends along the full ambient generated relation, and reflection lifts its successive intermediates through the same reconstructed corner representatives. Thus two displayed retained points represent the same point of Q exactly when their heights are equal and their original corner representatives are related by the full original corner relation. No relation correspondence or intermediate-point compatibility is assumed.

The representative parametrization is a homeomorphism from the original corner carrier times [0,1/4) onto D(nu), with its original induced topology. The dominant index is locally constant because its strict coordinate inequality persists on an open neighborhood. Its value and height are continuous, and the normalized inverse coordinates are continuous since their denominator never vanishes. Discreteness of the original tetrahedron tags makes D(nu) open. Full-chain saturation gives q inverse of U(nu) equal to D(nu); hence U(nu) is open in Q, and the original projection restricted over U(nu) is a quotient map.

Descend this same representative parametrization along the original corner quotient projection. The pinned quotient-map product descent applies because the half-open real height interval is locally compact. The exact relation comparison gives a continuous bijection from the original corner quotient times [0,1/4) to U(nu); the original restricted quotient map also proves continuity of its inverse. Compose with the earlier homeomorphism identifying the original corner quotient with the actual Cap(nu). This gives a homeomorphism Cap(nu) times [0,1/4) onto U(nu), with both subspaces inherited from the same original Q. At height zero the representative formula is precisely the earlier literal affine cap map, so the resulting collar fixes every actual cap point. In particular U(nu) contains Cap(nu).

This collar applies to arbitrary original finite discrete P, including self-gluings and repeated corner labels. It does not require a group-action presentation, orientability, genus, or no-edge-reversal. Surface charts on the cap still retain their separate no-edge-reversal condition. The collar supplies the actual boundary-neighborhood product bridge; interior and edge stars of the three-dimensional quotient, orientability, genus, marked-manifold identification and physical realization retain their separate obligations.

Application: the original six-tetrahedron pairing in main geometric-realization Section 17.1. Take T=Fin(6) and use precisely these directed face rows, with reverse directions given by inverse vertex permutations: (0,2) to (3,0), (3,2) to (4,0), (0,0) to (4,3), and (2,1) to (2,2) have image tuple (3,2,0,1); (1,0) to (5,2), (3,1) to (5,3), (5,0) to (1,2), and (1,3) to (2,0) have image tuple (2,3,1,0); (2,3) to (0,3) has image tuple (1,0,2,3); (4,1) to (1,1), (4,2) to (3,3), and (5,1) to (0,1) have image tuple (0,1,3,2). These rows specify the original RawFacePairing P through its faceEdge-slot permutations. The derived four-vertex sigma agrees with every displayed tuple and its inverse. The source edge order (01,02,03,12,13,23) and the canonical order (01,02,03,23,13,12) are related by slot conversion (0,1,2,5,4,3).

For this P, actual face-corner paths relate every original corner (t,j) to (0,0). Equality in the original Vertex quotient therefore identifies every vertex label with label(P,(0,0)). All twenty-four original corner triangles belong to this one label. This conclusion concerns the original generated corner relation and retains every tetrahedron and corner index.

Index the twenty-four closed triangles by the original corners (t,j). At j=0,1,2,3 use the respective cyclic orders (1,2,3), (0,3,2), (0,1,3), and (0,2,1) for the other vertices. Each original face crossing pairs the corresponding corner-triangle side with its actual target side. Sigma sends the source corner to the target corner, the omitted face to the target omitted face, and the two ordered side endpoints to the two target endpoints in reverse order. The resulting finite cyclic presentation has twenty-four triangular faces, seventy-two stored side occurrences, and thirty-six paired side labels. These side labels count edges of the triangle presentation, not global edges of the three-dimensional tetrahedron pairing.

The calibrated closed-triangle cell homeomorphism sends each polygonal cell to its original barycentric corner triangle, where beta_j=0, every coordinate is nonnegative, and their sum is one. On every full closed side, original transport is exactly the paired-side parametrization with parameter t replaced by 1-t. Both endpoints and all zero-coordinate ties are included. The twenty-four cell maps, indexed by the actual corner bijection, give a continuous bijection from the polygonal pre-realization to the original Point carrier at any original vertex label. Compactness of the finite cell sum and Hausdorffness of the original representative carrier make this a homeomorphism before quotienting.

Under that same representative homeomorphism, the original guarded Step holds exactly when the two polygonal representatives are related by an original polygon-gluing generator. One direction recovers the full closed side from its zero-coordinate guard; the other uses the actual paired side and reversed parameter. Transport through the full equivalence closures retains all intermediate representatives. Quotient congruence therefore identifies the complete original corner quotient with this exact twenty-four-triangle polygonal realization, with both original quotient topologies. Composing with the preceding original corner-to-cap homeomorphism gives a homeomorphism from the actual inherited cap image in the full retained-tetrahedron quotient to the same polygonal realization. At each original corner representative its retained point has x_j=3/4 and x_i=beta_i/4 for i different from j, so the comparison also fixes which original ambient quotient point it represents.

The same original twenty-four-triangle presentation has an explicit sequence of twenty-three face merges. At each step, the existing finite-cyclic ContextMerge comparison identifies two entire closed polygonal cells along their paired side and retains every other face. The source face permutation, signed side relabeling, cyclic rotation, and target presentation are specified at each step. Their realization homeomorphisms compose from the original triangle presentation to a single twenty-six-sided polygon; the construction therefore retains the original quotient topology throughout.

Label the terminal polygon sides by signed indices from zero through twelve. Its cyclic boundary word is (+9,+10,-5,-7,-4,-2,+8,-10,-1,+12,+0,+3,-9,-6,-11,-0,-12,-8,+2,+1,-3,+11,+6,+7,+5,+4), where a minus sign denotes the inverse orientation of the side with that index. Every index occurs once with each sign. The supplied signed polygon reduction uses three handle moves and seven adjacent inverse-side cancellations, followed by signed relabeling, to reach the canonical orientable word with three handles and no boundary component.

Applying the existing normalization realization homeomorphism gives a homeomorphism from the original twenty-four-triangle realization to the canonical closed orientable genus-three surface Quot(OrientableRel(3,0)). Composing with the original corner-to-cap and triangle-realization homeomorphisms identifies the actual inherited cap image in the full retained-tetrahedron quotient with this same surface. The original corner relation has one vertex label, so this conclusion applies to every original vertex-label choice and in particular to the label represented by (0,0).

This genus-three identification uses the complete signed face-merge and polygon-reduction comparisons. The separately marked manifold identification and genuine geometric realization retain their own obligations. All maps here apply the existing finite-cyclic, quotient and normalization suppliers; the application introduces no mathematical declaration or theorem Describe.

Application: the actual n-sheet cyclic covering in original Section 17.2. Retain precisely the original Section 17.1 pairing P of the preceding genus-three application, and fix any positive integer n, including n=1. Label its lifted tetrahedra by Fin(6) times ZMod n. On the original directed faces put v(4,1)=v(5,0)=1 and v(1,1)=v(1,2)=-1, with v(t,f)=0 on every other directed face. If P pairs (t,f) with (t',f'), the canonical lifted pairing P_n sends ((t,k),f) to ((t',k+v(t,f)),f'), with the integer voltage reduced in ZMod n. It uses exactly P's original three-edge-slot map, so its derived four-vertex permutation is literally the same sigma_(t,f). Opposite directed faces have opposite voltages; together with P's inverse laws this proves involutivity and inverse compatibility of the lifted pairing. Its tetrahedron index type has cardinality 6n.

Let R be the original retained tetrahedron of arrays alpha:Fin(4) -> Real satisfying 0<=alpha_i<=3/4 for every i and sum_i alpha_i=1. Use the raw carriers Fin(6) times R and (Fin(6) times ZMod n) times R, with discrete indices and the original real subspace topology. Write Q=TruncatedQuotient(P) and Q_n=TruncatedQuotient(P_n): each is the quotient by the full equivalence closure of its actual face moves guarded exactly by alpha_f=0, with its original quotient topology. Thus every cap, edge and coordinate tie remains present. Raw forgetting F_n((t,k),alpha)=(t,alpha) commutes with every face move and gives p_n:Q_n -> Q by p_n([((t,k),alpha)])=[(t,alpha)]. The fixed-sheet sections L_k(t,alpha)=((t,k),alpha) and F_n are continuous, with F_n L_0=id, so F_n is a quotient map. If q and q_n are the original quotient projections, p_n q_n=q F_n. Descent gives continuity of p_n, and this square of quotient maps proves that p_n is itself a surjective quotient map.

The sheet transport is exact on the original representatives: crossing face f from a=(t,alpha) sends L_k(a) to L_(k+v(t,f))(move_f(a)), where target coordinate i is alpha_(sigma_(t,f) inverse(i)). Every finite base equivalence chain therefore lifts from each prescribed initial sheet. Reversal uses the opposite voltage, and transitivity aligns the sheets at the common intermediate representative. Raw translation T_g((t,k),alpha)=((t,k+g),alpha) commutes with every face move and preserves the full lifted relation. It descends to Q_n with T_0=id, T_g T_h=T_(g+h), inverse T_(-g), and both directions continuous. Lifting a base chain and translating its endpoint sheet gives the exact criterion: F_n(x) and F_n(y) are base-related if and only if T_g(x) and y are lifted-related for some g in ZMod n. Passing to the literal quotients yields p_n(x)=p_n(y) if and only if T_g(x)=y for some g. Hence every full fiber is exactly one orbit of these actual sheet translations.

The edge calculation controls possible sheet returns in those full chains. In canonical local-edge order (01,02,03,23,13,12), use the integer potential p with tetrahedron rows (0,0,0,-1,0,0), (0,0,1,0,0,0), (0,0,0,0,0,0), (-1,-1,0,0,0,0), (-1,0,-1,-1,0,0) and (0,0,0,-1,0,-1). For every original directed face-edge port i to j across (t,f), the actual slot maps give p(j)=p(i)+v(t,f). Thus a lifted occurrence ((t,k),e) has invariant (c(t,e),k-p(t,e)), where c(t,e) in Fin(4) is its original global-edge class, ordered with degrees (12,8,8,8), and the potential is reduced in ZMod n. Each generator preserves this pair, and induction preserves it under the full generated edge relation. Conversely, at fixed corrected sheet s, lift every original occurrence (t,e) to ((t,s+p(t,e)),e). The same port equation lifts the original normalizing chains to their class roots, where p=0. Equality of the two invariant entries is therefore also sufficient for a full lifted edge chain. Consequently the actual lifted global-edge quotient is equivalent to Fin(4) times ZMod n and has 4n classes. Forgetting the sheet bijects the entire occurrence fiber of (c,s) with the original class-c fiber; its inverse reconstructs k=s+p(t,e). The four degrees remain 12,8,8,8 for every corrected sheet.

To prove freeness on Q_n, consider an arbitrary retained representative a=((t,k),alpha) related to T_g(a). Nonnegativity, sum one and the upper bound 3/4 force at least two nonzero coordinates. With all four coordinates nonzero, there is no legal face crossing and the full class of a is a singleton, so k+g=k. With exactly one zero coordinate, every legal first crossing uses that face. Its paired representative again has a unique zero, and its only next crossing is the original inverse. Induction through the full equivalence closure gives exactly the original representative or that paired representative. If the paired representative equals T_g(a), its base tetrahedron is again t. Every original face pairing returning to the same tetrahedron has voltage zero, including the pairing (2,1) with (2,2). Its sheet is therefore k, so again g=0. This handles the singleton and one-zero cases without restricting the length of the original chain.

In the remaining case exactly two coordinates are nonzero, and their indices determine a unique supporting local edge e. A legal zero-coordinate face misses both endpoints. The same original face-edge slot and sigma carry e to the supporting edge at the next representative and give an actual lifted edgeStep. The inverse face law makes the guarded relation symmetric, so a full ambient equivalence chain can be traversed as successive legal moves. Carrying the supporting edge at every intermediate representative produces a chain in the actual lifted edge relation. At T_g(a) the coordinate array is unchanged, so uniqueness of the support edge identifies its terminal edge with e. Preservation of the corrected sheet from the preceding edge calculation now gives k-p(t,e)=(k+g)-p(t,e) in ZMod n, and hence g=0. The support cases exhaust the full retained carrier, including all cap and edge ties. Equality T_g([a])=[a] in Q_n recovers just such an ambient chain, proving that these actual quotient translations act freely.

The finite discrete index type Fin(6) times ZMod n makes the lifted retained carrier compact and Hausdorff. The existing closed-relation theorem for arbitrary finite discrete raw face pairings applies to P_n on this entire carrier. The quotient by that closed full relation is compact and Hausdorff, so Q_n is also locally compact. We now have a finite additive group acting by continuous translations, with freeness proved above. The existing finite-action result gives proper discontinuity in this locally compact Hausdorff setting. Applying Mathlib's quotient-covering theorem to the actual quotient map p_n and its proved fiber-orbit equivalence gives an additive quotient-covering structure, and therefore IsCoveringMap(p_n). Thus the covering is a property of the original retained quotients Q_n and Q with their existing topologies.

Finally fix any b in Q and choose x_b in Q_n with p_n(x_b)=b, using surjectivity. The map g -> T_g(x_b) from ZMod n to the full fiber p_n inverse({b}) is onto by the fiber-orbit equivalence. It is one-to-one because equality of two translates, followed by inverse translation and freeness, forces their group elements to agree. Its inverse assigns to each fiber point the unique translating element. Hence the whole fiber is equivalent to ZMod n and, by its cardinality n, to Fin(n); explicitly Nat.card(p_n inverse({b}))=n for every b. This includes every cap point, every edge point and every coordinate tie, and for n=1 gives a single-point fiber. These are the exact n-sheet topological coverings of the original quotients. Identification of the full deck groups, Euler characteristics and pairwise nonhomeomorphism of the manifold family, and marked or physical identifications retain their separate obligations.

Application: path connectedness of the entire actual lifted quotient in original Section 17.2. Retain the same positive integer n, including n=1, the canonical lifted pairing P_n=Main17Cyclic1935.liftedPairing(n), and its tetrahedron type T_n=Fin(6) times ZMod n. The space Q_n is literally RawFaceCapSliceCandidate.TruncatedQuotient(P_n), the quotient of T_n times R by the full EqvGen of its original zero-coordinate TruncatedStep. Keep the discrete index topology, the real subspace topology on the complete closed retained tetrahedron R, their product topology and the resulting quotient topology. All caps, edges and coordinate ties remain in this space.

The corner path supplier applies to exactly the corner quotient used by the cap comparison. RawFaceLinkPathConnected and RawFaceCapSliceCandidate have definitionally identical chi, frame, sigma and cornerPairing for this same P_n, and hence identical Vertex, label, Carrier, Point, move and guarded Step. Their full EqvGen quotients and inferred quotient topologies agree as well. Thus the original product and subtype topologies on the corner representatives, and the quotient topology after identifying them, are retained throughout this bridge.

Reuse RawFaceLinkPathConnected.original_quotient_path_connected on that complete corner quotient at any actual label nu. Its paths lift original corner-label chains through actual crossing-face witnesses and join points within each convex corner triangle; concatenation keeps the same intermediate point. Since T_n is finite and discrete, RawFaceCapSliceCandidate.actualSliceQuotientHomeomorph transports these paths to the actual cap Cap_n(nu)=quotientSlice(P_n,nu), with its subspace topology inherited from Q_n. The comparison sends a corner representative ((t,j),beta) to the actual retained quotient class of (t,(3/4)e_j+(1/4)beta). Its full-chain reflection and slice saturation identify the complete corner relation with the ambient retained relation, and its restricted quotient-map argument supplies precisely this inherited topology. Consequently each such actual cap is path connected.

Fix the actual root label nu_0=label(P_n,((0,0),0)), with base tetrahedron zero, sheet zero and corner zero. Main17LiftedVertices2001.vertex_singleton identifies every label in this same actual lifted Vertex quotient with nu_0 for every positive n. Its source uses actual lifted corner-slot paths: iteration of the six-move corner loop of voltage one reaches every root sheet, and a root-to-corner path with its voltage correction reaches each requested corner. In particular label(P_n,(t,0))=nu_0 for every lifted tetrahedron tag t. The path-connected cap just obtained at nu_0 is therefore the one actual root cap needed for all these tags.

The complete retained carrier R is convex: convex combinations preserve each coordinate bound 0<=alpha_i<=3/4 and the sum-one equation. The literal anchor A=(3/4,1/12,1/12,1/12) belongs to R, since its entries satisfy those bounds and sum to one. For each tag t, its zeroth coordinate and the preceding actual label equality put (t,A) in Slice(P_n,nu_0), so q_n(t,A) belongs to Cap_n(nu_0). Convexity joins any alpha in R to A within the same retained tetrahedron. Map this path through the continuous constant-tag inclusion z -> (t,z) and then the actual continuous quotient projection q_n:T_n times R -> Q_n. This joins q_n(t,alpha) to its own anchor image in the full original Q_n.

For arbitrary retained representatives a=(t,alpha) and b=(u,beta), path connectedness of Cap_n(nu_0) joins their anchor images q_n(t,A) and q_n(u,A) inside that actual cap. Map this path into Q_n by the continuous cap subtype inclusion. Concatenate the quotient image of the path from a to its anchor, this included cap path, and the reverse of the quotient image of the path from b to its anchor. The endpoints match as actual points of Q_n, giving a path from q_n(a) to q_n(b) with its original quotient topology.

The class q_n((0,0),A) supplies a point of Q_n. Quotient induction on both arbitrary points reduces them to the representatives just treated, proving PathConnectedSpace(Q_n), and hence connectedness of the entire total space, for every positive n including n=1. Together with the preceding fiber and covering calculation, these are connected n-sheet topological coverings of the original retained quotient. Euler characteristics, pairwise nonhomeomorphism of the manifold family, identification of the full deck groups, and marked or physical identifications retain their separate obligations. This application reuses the checked suppliers and introduces no mathematical declaration or theorem Describe.

Application: a complete topological three-dimensional atlas for the original Section 17 quotients. Retain the literal six tetrahedra and single ideal-vertex class of Section 17.1, with the same actual pairing P, and the canonical pairing P_n on Fin(6) times ZMod n for every positive n, including n=1. The spaces are exactly Q=TruncatedQuotient(P) and Q_n=TruncatedQuotient(P_n). Their representatives retain all four coordinates between zero and three quarters with sum one, with the original real subspace topology and discrete tetrahedron indices. Their relations are the full EqvGen of the original face moves guarded by a zero face coordinate, and their topologies are the corresponding quotient topologies. The charts below apply to these complete spaces, including all cap, face and edge ties.

The original Section 17 base invariant rules out a full original dart chain from any unequal ordered root to its endpoint swap. This same condition follows for P_n by forgetting only the sheet: the dart (((t,k),j),l) maps to ((t,j),l), retaining both ordered endpoints. The actual sigma_lift identity says that the derived lifted vertex permutation is the base permutation, so forgetting commutes with every actual dart move. An original lifted DartStep therefore projects with its same crossing face and both endpoint exclusions to an original base DartStep. Induction through the full DartRelated EqvGen, including reflexivity, reversal and transitivity, projects every lifted chain. Forgetting also commutes with endpoint swap and preserves endpoint inequality. A lifted chain to the swapped root would consequently contradict the original base invariant. Thus no-edge-reversal holds at every actual ordered root of P_n, with no additional hypothesis on n.

Let C be the union of all actual labeled caps in Q, and let C_n be that union in Q_n. Membership in either union is equivalent, on every retained representative, to some original coordinate being three quarters; full-chain slice invariance makes this criterion independent of the representative. The actual vertex-singleton identity for P identifies C with the same cap at label(P,(0,0)). Its lifted counterpart identifies C_n with the same actual root cap at label(P_n,((0,0),0)). Thus the entire cap union is this one inherited cap subspace in each case. The one ideal-vertex class labels this full cap subspace.

Off the cap union every coordinate is strictly less than three quarters. The original representative then belongs to one of three strata: all four coordinates are positive, exactly one is zero, or exactly two are zero. Three zero coordinates would force the remaining coordinate to be one, contrary to the retained bound. In the last stratum the two nonzero coordinates sum to one and each lies strictly between one quarter and three quarters, so the point is in the interior of an actual retained edge. The original tetrahedron-interior charts, paired-face charts and cyclic edge-tube charts respectively supply open neighborhoods homeomorphic to open subsets of real three-space. The all-root no-edge-reversal condition supplies the edge case. These are neighborhoods in the full original quotient, using its full face relation and inherited quotient topology; together the three cases cover every point off the caps.

At every cap point, combine the actual cap plane chart with its collar Cap(nu) times [0,1/4) in the same full quotient. The collar keeps the original coordinates x_j=3/4-h and x_i=(1/4+h)p_i away from j, and fixes the actual cap at height zero. Restrict the resulting neighborhood to the original dominant-coordinate neighborhood of nu. There the union of all caps equals Cap(nu): full-chain invariance retains the dominant label, and uniqueness of a coordinate greater than one half identifies any cap index with that dominant index. The product plane chart and height band, with coordinates reordered as (h,u,v), give a homeomorphism onto an open subset of H3=EuclideanHalfSpace(3). Throughout its source, coordinate zero vanishes exactly on the full cap union. This includes every original corner and seam of the cap.

The complement of the full cap union is open, since its representative preimage is the intersection of the four strict inequalities alpha_i<3/4. Restrict each off-cap three-space chart to this complement. Carry real three-space into the positive-height part of H3 by sending coordinates (u,v,r) to (exp(r),u,v). This is a homeomorphism onto that open positive-height part, so the restricted chart still has open source and open target. Its height is strictly positive at every source point, and its source misses the full cap union. It therefore satisfies the same equivalence between zero chart coordinate and cap membership as the cap charts. The cap and off-cap constructions together cover the entire original quotient.

The earlier closed-relation result already makes Q and every Q_n compact and Hausdorff, or T2, for their original quotient topologies: their retained carriers have finite discrete indices, and the full original face equivalence relation is closed. Each open chart source is second countable because it is homeomorphic to an open subspace of H3, which is second countable. Compactness selects a finite subcover from these open chart sources. Pulling a countable basis back through each chart and taking the union over this finite cover gives a countable basis for the same full quotient topology. Thus both the base and every positive-degree quotient are second countable.

Each of these homeomorphisms between open subspaces extends to an OpenPartialHomeomorph from the same quotient to H3, with exactly its original open source and the same coordinate values there. Choose one through each point and take their range as the atlas. This gives a ChartedSpace H3 Q and, for every positive n including n=1, a ChartedSpace H3 Q_n on the existing topologies. For every chosen chart and every point in its source, coordinate zero vanishes if and only if that point belongs to the actual root cap: the cap at (0,0) for P and at ((0,0),0) for P_n. These are compact Hausdorff second-countable topological three-dimensional manifolds with boundary given by precisely those inherited caps. The preceding path-connectedness result applies to these same Q_n, so the actual n-sheet coverings have connected total manifolds for all positive n, including n=1.

Application: actual cap points have topological three-dimensional boundary charts in the same original full quotient. Retain finite discrete original tetrahedron indices and the original RawFacePairing, and impose the all-root no-edge-reversal condition used by the cap surface charts. For each original label nu and each actual point c of Cap(nu), there are an open neighborhood W of c in the full retained quotient Q, an open subset V of Mathlib EuclideanHalfSpace 3, and a homeomorphism from W onto V. A point of W belongs to the same actual Cap(nu) exactly when coordinate zero of its image is zero. This is an exact correspondence with the inherited original cap, including its corners and seams.

Choose an earlier plane chart A to B through c on that cap, with A relatively open in Cap(nu) and B open in the real plane. The collar sends A times [0,1/4) onto an open subset of U(nu), hence an open subset W of the same Q. View [0,1/4) as the open band h<1/4 in the nonnegative real half-line. The plane chart times this height-band identification gives W homeomorphic to the open set B times that band in the product of the real plane and the nonnegative half-line. The coordinate map ((u,v),h) to (h,u,v) identifies this product homeomorphically with Mathlib EuclideanHalfSpace 3, whose first L2 coordinate is nonnegative.

The boundary assertion uses both directions of the collar identification. Height zero maps to the original cap inclusion. Conversely, if a point of U(nu) lies on that same actual cap, its zero-height cap representative has the same ambient quotient point; injectivity of the collar forces its inverse height to be zero. The explicit three-coordinate homeomorphism preserves this height as coordinate zero, so the final chart has exactly the displayed cap boundary. The no-edge-reversal premise enters through the cap plane chart; the collar and height-band construction retain their independent scope. This establishes local charts near actual caps. The remaining interior and edge stars, orientability, genus, marked-manifold comparison and physical realization still require their separate bridges.

## References

- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.ActualQuotient`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.OpenDisk`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.Phi`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.Sector`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.Slice`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.TruncatedPoint`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.TruncatedQuotient`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.TruncatedStep`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.TruncatedTetrahedron`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actualOpenDiskChart`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actualSeamQuotientHomeomorph`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actualSliceHomeomorph`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actualSliceQuotientHomeomorph`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actual_eqvgen_iff`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actual_full_fan_correspondence`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actual_open_quotient_neighborhood`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actual_slice_carriers`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actual_slice_eqvgen_iff`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actual_slice_step_iff`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actual_step_iff`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actual_strict_coordinates`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.alpha`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.beta`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.closedInput`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.coordinateEquiv`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.coordinateHomeomorph`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.quotientNeighborhood`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.quotientSlice`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.rawPhi`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.seam`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.sector_count_neZero`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.swap`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.toTruncation`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.truncatedMove`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.vertex`
- Dependency: [D5/S3/Geometry/Gluing/ActualCornerPointPeriods](ActualCornerPointPeriods.md)
- Dependency: [D5/S3/Geometry/Gluing/CyclicTriangleDisk](CyclicTriangleDisk.md)
