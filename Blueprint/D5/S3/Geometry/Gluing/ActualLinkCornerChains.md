# Actual guarded corner chains

## Abstract

Original affine link chains: exact interior and positive-side classes, strict-region saturation and restriction.

**Definition 1.1 (The original whole-face permutations).**

$$\forall f \in Fin\left(4\right),\; \forall i \in Fin\left(4\right),\; facePerm\left(f, i\right) = lookup\left(((3, 0, 1, 2), (3, 2, 0, 1), (2, 3, 1, 0), (1, 2, 3, 0)), f, i\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.facePerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four rows are p=(3,0,1,2), q=(3,2,0,1), q inverse and p inverse. The private frozen_face_data proof compares these whole-face maps with the published facePair and slotMap on each actual face slot.

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

**Definition 1.4 (Tagged barycentric coordinates).**

$$\forall Omega \in Type,\; Raw\left(Omega\right) = Omega \times Fin\left(4\right) \times Functions\left(Fin\left(4\right), R\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Raw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A raw representative has an actual corner (omega,j) and four real barycentric coordinates.

**Definition 1.5 (The complete original corner triangle).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall x \in Raw\left(Omega\right),\; x \in Carrier\left(u, v, nu\right) \Leftrightarrow \left(coordinate\left(x, second\left(corner\left(x\right)\right)\right) = 0 \land \left(\left(\forall i \in Fin\left(4\right),\; 0 \le coordinate\left(x, i\right)\right) \land \left(sumCoordinates\left(x\right) = 1 \land label\left(pairing\left(u, v\right), corner\left(x\right)\right) = nu\right)\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Carrier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate at j is zero, every coordinate is nonnegative, and their sum is one. The actual corner label is the fixed nu from the frozen Pairing quotient. Boundary ties remain in this closed carrier.

**Definition 1.6 (The actual carrier subtype).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; Point\left(u, v, nu\right) = Subtype\left(Carrier\left(u, v, nu\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Point` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Representatives carry all closed-carrier conditions and the same actual corner-class tag.

**Definition 1.7 (Original affine face transport).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall f \in Fin\left(4\right),\; \forall x \in Raw\left(Omega\right),\; move\left(u, v, f, x\right) = ((act\left(first\left(corner\left(x\right)\right), faceWord\left(u, v, f\right)\right), apply\left(facePerm\left(f\right), second\left(corner\left(x\right)\right)\right)), pullback\left(facePerm\left(f\right), coordinates\left(x\right)\right))$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.move` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transport the sheet by the exact source word, the omitted corner by the whole-face permutation, and the coordinate vector by its inverse. No endpoints are sorted.

**Definition 1.8 (A permitted affine image in the same actual corner class).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall x \in Point\left(u, v, nu\right),\; \forall f \in Fin\left(4\right),\; f \neq second\left(corner\left(x\right)\right) \Rightarrow value\left(pairedPoint\left(u, v, x, f\right)\right) = move\left(u, v, f, value\left(x\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.pairedPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input requires f different from the omitted corner j. The carrier proof directly consumes the published actual_step helper at its original owner, after extending the original face-slot table. The sum and coordinate conditions are preserved by the whole-face permutation. This definition constructs the affine image even away from a side; the Step relation separately imposes the zero guard.

**Definition 1.9 (Only the original guarded link generators).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall x \in Point\left(u, v, nu\right),\; \forall y \in Point\left(u, v, nu\right),\; Step\left(u, v, x, y\right) \Leftrightarrow \left(\exists f \in Fin\left(4\right),\; f \neq second\left(corner\left(x\right)\right) \land \left(coordinate\left(x, f\right) = 0 \land value\left(y\right) = move\left(u, v, f, value\left(x\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A step requires f different from j and beta(f)=0, and its target is the displayed affine image. The identically zero omitted-corner coordinate creates no fourth side.

**Definition 1.10 (The full original affine equivalence closure).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall x \in Point\left(u, v, nu\right),\; \forall y \in Point\left(u, v, nu\right),\; Related\left(u, v, x, y\right) \Leftrightarrow EqvGen\left(Step\left(u, v\right), x, y\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Related` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take EqvGen of Step on the entire closed carrier. No chart region, assumed cycle or radial-map kernel defines this relation.

**Definition 1.11 (Ordered endpoint data).**

$$\forall Omega \in Type,\; Dart\left(Omega\right) = Omega \times Fin\left(4\right) \times Fin\left(4\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Dart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The raw ordered occurrence is ((omega,j),k). Actual corner neighborhoods have j different from k because beta(j)=0 and beta(k)>1/2. The data type retains every order, including (3,0).

**Definition 1.12 (The same whole-face transport on ordered endpoints).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall d \in Dart\left(Omega\right),\; \forall f \in Fin\left(4\right),\; dartMove\left(u, v, f, d\right) = ((act\left(sheet\left(d\right), faceWord\left(u, v, f\right)\right), apply\left(facePerm\left(f\right), firstEndpoint\left(d\right)\right)), apply\left(facePerm\left(f\right), secondEndpoint\left(d\right)\right))$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.dartMove` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both j and k move by the actual face permutation; the sheet moves by the actual word.

**Definition 1.13 (Original oriented edge-incidence transport).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall d \in Dart\left(Omega\right),\; \forall e \in Dart\left(Omega\right),\; DartStep\left(u, v, d, e\right) \Leftrightarrow \left(\exists f \in Fin\left(4\right),\; f \neq firstEndpoint\left(d\right) \land \left(f \neq secondEndpoint\left(d\right) \land e = dartMove\left(u, v, f, d\right)\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.DartStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A dart step may use only a face omitting neither endpoint. This is a generated incidence relation, not an assumed cyclic enumeration.

**Definition 1.14 (The actual ordered-dart component).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall d \in Dart\left(Omega\right),\; \forall e \in Dart\left(Omega\right),\; DartRelated\left(u, v, d, e\right) \Leftrightarrow EqvGen\left(DartStep\left(u, v\right), d, e\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.DartRelated` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The equivalence closure is generated by the actual guarded endpoint moves. This delivery does not enumerate its component by Fin(3r).

**Definition 1.15 (Strict corner regions from an actual endpoint component).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall d \in Dart\left(Omega\right),\; \forall x \in Point\left(u, v, nu\right),\; x \in Neighborhood\left(u, v, d\right) \Leftrightarrow \left(\exists k \in Fin\left(4\right),\; \frac{1}{2} < coordinate\left(x, k\right) \land DartRelated\left(u, v, d, (corner\left(x\right), k)\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Neighborhood` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A representative is selected when some beta(k)>1/2 and its ordered dart is in the actual component of the selected seed. The strict inequality excludes boundary ties from this region while retaining them in Carrier. This delivery proves saturation and chain reflection; it does not yet prove openness or a disk coordinate.

**Definition 1.16 (Interior coordinates).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall x \in Point\left(u, v, nu\right),\; Interior\left(x\right) \Leftrightarrow \left(\forall f \in Fin\left(4\right),\; f \neq second\left(corner\left(x\right)\right) \Rightarrow coordinate\left(x, f\right) \neq 0\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Interior` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every non-omitted coordinate is nonzero. On the nonnegative closed carrier this means each of those three coordinates is positive.

**Definition 1.17 (A unique active side).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall x \in Point\left(u, v, nu\right),\; \forall f \in Fin\left(4\right),\; EdgePoint\left(x, f\right) \Leftrightarrow \left(f \neq second\left(corner\left(x\right)\right) \land \left(coordinate\left(x, f\right) = 0 \land \left(\forall g \in Fin\left(4\right),\; \left(g \neq second\left(corner\left(x\right)\right) \land coordinate\left(x, g\right) = 0\right) \Rightarrow g = f\right)\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualLinkCornerChains.EdgePoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exactly one non-omitted coordinate is zero. The other two are nonzero and, on this carrier, positive.

**Theorem 1.18 (Source-specific normal forms and full-chain restriction).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall nu \in Vertex\left(pairing\left(u, v\right)\right),\; \forall x \in Point\left(u, v, nu\right),\; \forall y \in Point\left(u, v, nu\right),\; \left(Interior\left(x\right) \Rightarrow \left(Related\left(u, v, x, y\right) \Leftrightarrow y = x\right)\right) \land \left(\left(\forall f \in Fin\left(4\right),\; EdgePoint\left(x, f\right) \Rightarrow \left(pairedPoint\left(u, v, x, f\right) \neq x \land \left(Related\left(u, v, x, y\right) \Leftrightarrow \left(y = x \lor y = pairedPoint\left(u, v, x, f\right)\right)\right)\right)\right) \land \left(\left(\forall d \in Dart\left(Omega\right),\; Related\left(u, v, x, y\right) \Rightarrow \left(x \in Neighborhood\left(u, v, d\right) \Leftrightarrow y \in Neighborhood\left(u, v, d\right)\right)\right) \land \left(\forall d \in Dart\left(Omega\right),\; \left(x \in Neighborhood\left(u, v, d\right) \land y \in Neighborhood\left(u, v, d\right)\right) \Rightarrow \left(Related\left(u, v, x, y\right) \Leftrightarrow EqvGen\left(StepRestrictedTo\left(u, v, Neighborhood\left(u, v, d\right)\right), subtype\left(x\right), subtype\left(y\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/ActualLinkCornerChains.actual_guarded_point_analysis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every group, arbitrary right action, u and v, actual corner class nu, and original representatives x and y: an interior x has singleton class; an EdgePoint has exactly x and its distinct original paired image as its class; every strict component neighborhood is invariant under the full EqvGen; and restriction to that neighborhood reflects the full relation. The positive-side proof constructs a two-point invariant from the unique active guard and inverse pairing. It then inducts through all four EqvGen constructors. Saturation is established before the restriction proof, whose transitive case explicitly transports membership to the intermediate representative. These are new original-carrier deductions, not applications of an assumed cycle or assumed relation correspondence. The helpers are consumed on these live proof paths. The remaining local obligations are the four minimal point-period Fin(3r) enumerations, the exact origin-cycle and fan-seam correspondence, openness with the actual quotient-subspace topology, the supplied fan radial chart at the same actual vertex, and the geometric truncation-slice chain and topology comparison. Global orientability, genus, marked-manifold realization and metric statements remain outside this result. No external novelty is claimed.

## References

- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Carrier`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Dart`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.DartRelated`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.DartStep`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.EdgePoint`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Interior`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Neighborhood`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Point`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Raw`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Related`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.Step`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.actual_guarded_point_analysis`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.dartMove`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.facePerm`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.faceWord`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.move`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.pairedPoint`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualLinkCornerChains.reverseFace`
- Dependency: [D5/S3/Geometry/Hyperideal/NoncommutativeCornerOrbits](../Hyperideal/NoncommutativeCornerOrbits.md)
