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

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall x \in Omega,\; vertex\left(u, v, c, x\right) = label\left(pairing\left(u, v\right), first\left(encode\left(u, v, c, (x, 0)\right)\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vertex is the original pairing label of the corner of encode(u,v,c,(x,0)). All four rows retain the source order L0, L1, H2, H0, and ordered pairs such as (3,0) are not sorted.

**Definition 1.4 (Finite occurrence coordinates).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall x \in Omega,\; \forall z \in Fin\left(3 \times pointPeriod\left(u, v, c, x\right)\right) \times Sector,\; rawPhi\left(u, v, c, x, z\right) = (first\left(occurrence\left(u, v, c, x, first\left(z\right)\right)\right), beta\left(c, second\left(iterate\left(tour\left(u, v, c\right), value\left(first\left(z\right)\right), (x, 0)\right)\right), value\left(second\left(z\right)\right)\right))$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.rawPhi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index lies in Fin(3r), where r is the minimal point period of the original row return word at x. Its actual dart is occurrence(u,v,c,x,i). The phase of the corresponding iterate of tour determines the incoming and outgoing face coordinates. No return of the full transported frame is required.

**Definition 1.5 (The strict original neighborhood).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall x \in Omega,\; Finite\left(Omega\right) \Rightarrow \left(\forall z \in Fin\left(3 \times pointPeriod\left(u, v, c, x\right)\right) \times Sector,\; member\left(Phi\left(u, v, c, x, z\right), Neighborhood\left(u, v, vertex\left(u, v, c, x\right), encode\left(u, v, c, (x, 0)\right)\right)\right) \land underlyingRaw\left(Phi\left(u, v, c, x, z\right)\right) = (first\left(occurrence\left(u, v, c, x, first\left(z\right)\right)\right), beta\left(c, second\left(iterate\left(tour\left(u, v, c\right), value\left(first\left(z\right)\right), (x, 0)\right)\right), value\left(second\left(z\right)\right)\right))\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkAffineFan.Phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrict a and b to nonnegative reals with a+b<1. The constructed raw point lies in the original Carrier at the actual seed vertex and in Neighborhood of the actual seed dart. Its ordered tip has barycentric coordinate strictly greater than one half. The cutoff a+b=1 is outside this chart; it is not removed from the ambient carrier.

**Theorem 1.6 (Unique actual occurrence and affine coordinates).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall x \in Omega,\; Finite\left(Omega\right) \Rightarrow Bijective\left(Phi\left(u, v, c, x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actual_strict_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any group G, any finite set Omega with a right G action, any u and v, any one of the four rows, and any root x, Phi bijectively parametrizes the genuine strict original neighborhood. There is no assumption that G is finite, that the action is faithful, free, transitive or regular, or that the return word has finite group order.

The inverse first finds the unique barycentric coordinate greater than one half. The original ordered-dart component enumeration then determines the unique occurrence index. The two real coordinates are twice the original incoming and outgoing barycentric coordinates. The simplex equation and zero omitted-corner coordinate prove that their sum is strictly less than one and reconstruct every original barycentric entry.

The original pairedPoint construction transports the corner label along each guarded dart step; EqvGen induction transports it along the complete dart component. This puts Phi at the same actual link vertex, not at an independently chosen label. The finite-period supplier covers singleton period one, giving three occurrences, as well as nonfaithful and nonregular actions.

This result constructs coordinates before quotienting. It does not prove that original affine Step is a cyclic seam or its reverse, identify full affine EqvGen with the cyclic fan relation, prove continuity of these coordinates, or give the saturated quotient open disk chart. The original truncation-slice comparison and the global orientability, closedness, genus and geometric conclusions remain separate.

The source is the actual link application accompanying supplement 122.3 of the group-transport construction. ActualCornerPointPeriods supplies the entire original dart component, and ActualLinkCornerChains supplies the original guarded affine carrier. The cyclic fan disk theorem is an existing further supplier; no generic circle or disk theorem is proved here. No literature-priority claim is made.

## References

- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.Phi`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.Sector`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.actual_strict_coordinates`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.beta`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.rawPhi`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkAffineFan.vertex`
- Dependency: [D5/S3/Geometry/Gluing/ActualCornerPointPeriods](ActualCornerPointPeriods.md)
