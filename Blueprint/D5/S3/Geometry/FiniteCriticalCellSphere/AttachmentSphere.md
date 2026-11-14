# The attachment quotient and its sphere

## Abstract

Literal attachment quotients, the separate singleton branch, and based sphere comparison.

An Attachment consists of X=P union simplex(face), intersection P intersect simplex(face)=boundary(face), a nonempty face and a based contraction of the core P at p. Write Q=X/P and q for the core quotient. AttachmentCollar supplies the inverse quotientInverse and the based quotientEquivalence. Closed pasting and quotient descent compare Q with a sphere of dimension face.card-1.

For at least two face labels, choose a simplex vertex; vertex_boundary gives its zero coordinate at a different face label. Paste its full-boundary class on coreSet with the diskRestrict class on diskSet. The seam follows from diskIn_mem_core_iff and diskIn_restrict. This continuous map is constant on the collapsed core and descends to Q. In the other direction lift q after diskIn. Quotient induction reduces the inverse laws to classMap_toQ on the closed cover and classMap_disk on disk points.

For a singleton face, mass one over its unique label gives coordinate one, so BDisk is empty. The core and disk are disjoint closed covering pieces. Paste false on the core and true on the disk, then descend through q. Its inverse sends false to q(basepoint) and true to q(diskIn(vertex)). Singleton disk uniqueness supplies the disk-side inverse; p supplies the nonempty core class. Thus Q has two classes even though the singleton simplex modulo its empty boundary has one point.

**Definition 1.1 (The full-boundary quotient map into Q).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.simplexQuotientToQ`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.simplexQuotientToQ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Quotient.lift sends the boundary class of x to q(diskIn(x)); boundary points lie in coreSet by the intersection equation. This is the inverse map of quotientSimplexHomeomorph. It is defined on singleton faces too.

**Definition 1.2 (The actual quotient comparison for at least two labels).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.quotientSimplexHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.quotientSimplexHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward is qToSimplexQuotient, a Quotient.lift of the closed-cover classMap; the backward is simplexQuotientToQ. classMap_toQ and classMap_disk give the two inverse equations on representatives. The hypothesis 2 <= Fintype.card face supplies a boundary vertex.

**Definition 1.3 (The rational Euclidean comparison).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.multiSphereHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.multiSphereHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose quotientSimplexHomeomorph with FiniteSimplexBoundarySphere.simplexBoundaryStdSphere. The latter uses psi, its quotient map and L2 isometric reindexing. The cardinality of the face subtype equals the finset cardinality, giving StdSphere(face.card-1).

**Definition 1.4 (The nonempty core and isolated original disk vertex).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singletonQuotientHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singletonQuotientHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward is qBool, the quotient lift of the closed-cover Bool map. The backward chooses q(basepoint) or q(diskIn(singletonVertex)). The inverse equations follow from the cover, core quotient relation and singleton disk uniqueness.

**Definition 1.5 (Reuse the two-point realization and sphere comparison).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singletonSphere0Homeomorph`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singletonSphere0Homeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose singletonQuotientHomeomorph with FiniteComponentClosure.boolTwoPointHomeomorph from BasedJoin, then with FiniteComponentClosure.twoPointSphereHomeomorph from Transport. These maps send a Bool to its coordinate vertex of twoPoints, then use coordinate true minus coordinate false in the one-dimensional Euclidean sphere.

**Definition 1.6 (The exact natural dimension).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singletonSphereHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singletonSphereHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transport the equality face.card-1=0 in singletonSphere0Homeomorph to obtain the sphere in the dimension specified by the face.

**Definition 1.7 (Both nonempty-face branches).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Split on face.card=1. The other branch has at least two labels by face_nonempty. Both branches give Q homeomorphic to StdSphere(face.card-1). Empty faces are excluded by the Attachment assumptions.

**Definition 1.8 (The image of the original included p).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereBasepoint`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereBasepoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The chosen sphere point is sphereHomeomorph(q(basepoint)), where basepoint is the inclusion of p into X.

**Definition 1.9 (Reuse the original based composition).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereEquivalence`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereEquivalence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply FiniteComponentClosure.basedTrans to quotientEquivalence and basedHomeomorphism of sphereHomeomorph. If h is sphereHomeomorph and s is quotientInverse, the forward map is h after q and the backward map is s after h.symm. The two inverse homotopies fix basepoint and sphereBasepoint respectively. HomotopyRel.trans rescales two time intervals, so composition with the constant inverse homotopies of a homeomorphism can introduce stationary segments.

Original Certificate application. For c : FiniteAlexanderDualCollapse.Certificate V, set X=c.X, P=c.P and face=c.lambda=W minus sigma. Use c.arithmetic.1 for face nonemptiness, c.cell_decomposition for the exact union and c.cell_intersection.1 for the full ordinary boundary. Choose p by including conePoint c.a c.Dstar into c.P and use the computed standalone c.pContraction. c.collapseP remains a collapse of P alone; its free pairs are never asserted free in X.

The original attaching map remains c.j : C(Space c.Dstar, Space c.Estar), the existing realizationInclusion with unchanged coordinates. The original realization of K is Space c.K for c.K=c.Estar union c.C. Its chosen apex is the literal inclusion of conePoint c.a c.Dstar into c.K. The reduction uses exactly c.reductionSDR.retraction : C(Space c.K, Space c.X) and c.reduction.inclusion in the other direction. The retraction-inclusion identity and the reversed whole-retained-endpoint SDR give a based equivalence at that original apex; compose it with the attachment sphere equivalence using the same original basedTrans.

For that application the literal forward is sphereHomeomorph after q after c.reductionSDR.retraction. The backward is c.reduction.inclusion after quotientInverse after sphereHomeomorph.symm. The target is exactly StdSphere c.d, with c.d=c.lambda.card-1. The left homotopy runs from backward after forward to the identity on Space c.K; the right runs from forward after backward to the identity on StdSphere c.d. They fix the original apex and its actual sphere point at every time. The original reduction homotopy still fixes every included point of c.X. No equality to a different time parametrization is used.

The disk map extends the original lambda coordinates by zero, and the reduction inclusion changes no coordinates. Thus an included disk representative in K retains every lambda coordinate and has zero at labels outside lambda. Separately, if v is outside insert c.a c.W, every point of the original K has zero v-coordinate: K is Estar union cone(c.a,Dstar), and each face is supported in insert c.a c.W. This sufficient uniform guard applies also to the SDR outputs and included points. It does not characterize every ghost label; ambient ghost labels can lie inside W. A core vertex outside lambda need not have zero coordinate there. The construction adds no hypothesis on the Certificate and asserts no homotopy equivalence of its attaching map j.

## References

- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.multiSphereHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.quotientSimplexHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.simplexQuotientToQ`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singletonQuotientHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singletonSphere0Homeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singletonSphereHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereBasepoint`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereEquivalence`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereHomeomorph`
- Dependency: [D5/S3/Geometry/FiniteComponentClosure/BasedJoin](../FiniteComponentClosure/BasedJoin.md)
- Dependency: [D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar](AttachmentCollar.md)
