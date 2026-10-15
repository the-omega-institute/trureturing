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
