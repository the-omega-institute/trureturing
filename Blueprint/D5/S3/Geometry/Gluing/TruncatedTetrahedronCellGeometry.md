# Retained tetrahedron cell geometry

## Abstract

The original retained quotient has exact ambient fibers and complete closed ball reconstructions.

**Theorem 1.1 (Full fibers and reconstruction of every closed cell).**

$$\forall T \in Types,\; [Fintype\left(T\right)] [TopologicalSpace\left(T\right)] [DiscreteTopology\left(T\right)] \forall P \in RawFacePairing\left(T\right),\; \left(\forall a \in TruncatedPoint\left(T\right),\; \forall b \in TruncatedPoint\left(T\right),\; Interior\left(a\right) \Rightarrow \left(q\left(P\right)\left(a\right) = q\left(P\right)\left(b\right) \Leftrightarrow b = a\right)\right) \land \left(\left(\forall a \in TruncatedPoint\left(T\right),\; \forall b \in TruncatedPoint\left(T\right),\; \forall f \in Fin\left(4\right),\; FaceInterior\left(a, f\right) \Rightarrow \left(\left(truncatedMove\left(P, f, a\right) = a \Rightarrow False\right) \land \left(q\left(P\right)\left(a\right) = q\left(P\right)\left(b\right) \Leftrightarrow \left(b = a \lor b = truncatedMove\left(P, f, a\right)\right)\right)\right)\right) \land \left(\left(\forall t \in T,\; \exists h \in Homeomorph\left(Disk\left(3\right), TruncatedTetrahedron\right),\; \forall x \in Disk\left(3\right),\; bulkDiskPoint\left(t, x\right) = pair\left(t, h\left(x\right)\right)\right) \land \left(\forall k \in FaceShape,\; \forall t \in T,\; \forall j \in Fin\left(4\right),\; \exists h \in Homeomorph\left(Disk\left(2\right), Subtype\left(faceCarrier\left(k, t, j\right)\right)\right),\; \forall x \in Disk\left(2\right),\; faceDiskPoint\left(k, t, j, x\right) = val\left(h\left(x\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/TruncatedTetrahedronCellGeometry.cell_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Quantify over every universe-level type T, every Fintype T dictionary finiteT, every topology topologyT on T, every DiscreteTopology T topologyT dictionary discreteT, and every RawFacePairing P on T. T may be empty. The pairing consists of the original fixed-point-free involution P.facePair on T times Fin 4 and the mutually inverse three-slot permutations P.faceMap. These are the complete theorem inputs; no quotient topology or cell structure is supplied.

The retained-quotient definitions use the namespace TruncatedTetrahedronRelativeCW. TruncatedPoint T is exactly ActualLinkAffineFan.TruncatedPoint T, namely T times the subtype of four real coordinates in [0,3/4] with sum one. Its topology is the original product and subtype topology. The frame and sigma maps are those of RawFaceLinkPathConnected. truncatedMove P f transports the tag by P.facePair and all four coordinates by inverse sigma. TruncatedStep P a b means that some coordinate f of a is zero and b is that transported point. TruncatedQuotient P is the quotient by the entire Relation.EqvGen of this step, with its original quotient topology. q P is the original Quotient.mk' projection.

Interior a means that all four coordinates of a are nonzero. FaceInterior a f means that coordinate f is zero and every zero coordinate is f. The first clause quantifies over every a and b in the full retained carrier: if Interior a, equality of their quotient projections is equivalent to b=a. The second clause also quantifies over every f in Fin 4: if FaceInterior a f, its transported mate differs from a and equality of projections is equivalent to b=a or b=truncatedMove P f a. This includes self-pairings of faces in one tetrahedron. No restriction to one face or to the interior is imposed on b.

Disk d is the subtype of the closed unit ball centered at zero in Fin d -> R, with its inherited topology. TruncatedTetrahedron is the original closed four-coordinate subtype without a tag. FaceShape has exactly hex and cap. faceCarrier k t j consists of all retained points with tag t and coordinate j equal to zero for hex, or 3/4 for cap; every lower-dimensional boundary tie is included.

The bulk reconstruction clause gives, for each t in T, a homeomorphism h from the entire Disk 3 to the entire TruncatedTetrahedron such that bulkDiskPoint t x=(t,h x) for every x in Disk 3. The face reconstruction clause gives, for each k,t,j, a homeomorphism h from the entire Disk 2 onto the subtype faceCarrier k t j such that faceDiskPoint k t j x is the underlying retained point of h x for every disk point. These are equalities for the prescribed original reconstructions, not merely existence of some parametrizations. They imply full closed-carrier coverage, including all boundary points.

For the proof, the original coordinate models retain three or two coordinates and recover the last as the prescribed mass minus their sum. The bulk and hex models have mass one, the cap model mass 1/4, and each retained coordinate lies in [0,3/4]. Closedness, compactness, convexity and nonempty strict interiors give Mathlib's ambient convex-body homeomorphism carrying the whole body, its interior and frontier to the closed ball, open ball and sphere. bulkHomeomorph and faceHomeomorph reconstruct the original coordinates. The two reconstruction witnesses are the composites of the inverse ball homeomorphisms with those actual affine homeomorphisms. The fiber proofs use the full original zero-guarded equivalence closure; the single-zero class consists exactly of the original point and its distinct transported mate.

In the formula, Types denotes the chosen universe of types, Fintype(T) the finite enumeration dictionary type, TopologicalSpace(T) its topology type, and DiscreteTopology(T,topologyT) the corresponding discrete-topology dictionary type. Homeomorph(A,B) denotes A equiv_t B with the topologies just specified; pair(t,z) is the original product constructor, and val removes exactly one subtype layer. Every quantifier over a,b is over TruncatedPoint T, every f,j is in Fin 4, k is in FaceShape, and each disk quantifier includes its closed-ball subtype proof. The four displayed clauses are precisely CellGeometry P (q P).

TruncatedTetrahedronRelativeCW.upper_geometry consumes the two fiber clauses directly. Its topCell_closed_image and directedFaceCell_closed_image proofs consume the two reconstruction witnesses through their surjectivity and pointwise equalities. The supplier also owns the unchanged compact/open chart machinery and original Hausdorff quotient argument used by that assembly. This theorem establishes the retained geometric input to the upper relative complex; an absolute CW structure and an Euler invariant require further results.

## References

- Truth anchor: `D5/S3/Geometry/Gluing/TruncatedTetrahedronCellGeometry.cell_geometry`
- Dependency: [D5/S3/Geometry/Gluing/ActualLinkAffineFan](ActualLinkAffineFan.md)
- Dependency: [D5/S3/Geometry/Gluing/FiniteZeroGuardedClosure](FiniteZeroGuardedClosure.md)
- Dependency: [D5/S3/Geometry/Gluing/RawFaceLinkPathConnected](RawFaceLinkPathConnected.md)
