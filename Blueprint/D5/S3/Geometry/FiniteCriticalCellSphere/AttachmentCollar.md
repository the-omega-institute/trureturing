# The attachment collar and core quotient

## Abstract

The attachment collar and core quotient.

Retain the original ambient labels, a nonempty face, X=P union simplex(face), the exact full-boundary intersection and a standalone based contraction of P to its actual p. The moving seam is c(s)=1-s/2. Two closed pastings construct the literal collar and its endpoint inverse, with both homotopies based at coreIn(p). Face-coordinate transport, the boundary bridge, the finite minimum and cardinality determine these displayed maps.

The singleton face is included throughout: its ordinary full boundary is empty and no genuine boundary point is chosen. This module does not identify any quotient with a sphere. All extrema range only over original face labels, and every L2 formula is transported through the existing coordinate homeomorphism without identifying a plain-function norm with the Euclidean norm.

**Definition 1.1 (Closed-cover pasting).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.pasteClosed`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.pasteClosed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Paste two continuous maps on a closed cover, using their equality on the intersection. The continuity proof applies continuousOn union_of_isClosed to construct diskCollar and collar.

**Theorem 1.2 (Evaluate the first closed branch).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.pasteClosed_left`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.pasteClosed_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluation on the first closed set follows from the dependent-if definition. diskCollar_inner and collar_core_apply consume this branch law.

**Theorem 1.3 (Evaluate the second closed branch).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.pasteClosed_right`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.pasteClosed_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluation on the second closed set uses the supplied seam equality when both branches apply. diskCollar_outer and collar_disk_apply consume it.

**Definition 1.4 (Actual-coordinate attachment input).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.Attachment`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.Attachment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input consists of native X and P on the unchanged finite ambient type, a nonempty face, the exact union X=P union simplex(face), exact intersection P intersect simplex(face)=boundary(face), an actual point p of P, and a HomotopyRel contraction of P to p fixing p. The sole allowed homotopy input is this standalone based contraction of P to p fixing p. No contraction of X, desired sphere equivalence, collar or freeness across X is assumed.

**Definition 1.5 (A point of the face label type).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.faceInhabited`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.faceInhabited` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nonempty face data supplies a Nonempty instance for its original-label subtype. This orders no labels and deletes no ambient ghosts.

**Definition 1.6 (The existing L2 simplex).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.Disk`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.Disk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Disk is Simplex on the subtype of original face labels, with nonnegative coordinates and mass one.

**Definition 1.7 (The full boundary subspace).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.BDisk`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.BDisk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

BDisk is the subtype of disk points having a zero coordinate at some face label. It is empty for a singleton face.

**Definition 1.8 (The literal realized core in X).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreSet`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A point of the original realization of X lies in coreSet exactly when its same coordinate vector lies in the realization of P.

**Definition 1.9 (The literal realized attached disk).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskSet`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A point of X lies in diskSet exactly when its original coordinate vector lies in faceSimplex(face), including support zero at every ambient label outside face.

**Theorem 1.10 (Original core containment).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.core_le`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.core_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact union gives P contained in X; coreIn uses this containment for the literal realizationInclusion.

**Theorem 1.11 (Original simplex containment).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.simplex_le`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.simplex_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact union places the actual face simplex in X. disk_mem consumes this containment.

**Definition 1.12 (The unchanged core inclusion).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreIn`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreIn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing realizationInclusion is used for P into X, with containment derived from the exact union.

**Definition 1.13 (The actual included basepoint).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.basepoint`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.basepoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The basepoint of X is the literal core inclusion of the supplied point of P.

**Theorem 1.14 (The native realized simplex).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.simplex_realization`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.simplex_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ordinary realization of the nonempty finite simplex is the existing ambient faceSimplex, with unchanged coordinates and support. diskIn_mem_core_iff consumes the identity.

**Theorem 1.15 (Range of the included disk).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.disk_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.disk_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing faceCoordinateHomeomorph supplies the actual face point and simplex_le places its support face in X. This is the range proof of diskIn.

**Definition 1.16 (Zero extension into the original X).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskIn`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskIn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The disk map uses the existing faceCoordinateHomeomorph, extending the L2 face coordinates by zero in all original ambient coordinates, then includes that actual face in X.

**Definition 1.17 (Restriction to the literal core).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreRestrict`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreRestrict` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An actual core-set point is viewed as a point of Space P without changing its coordinate vector. coreCylinderMap and the core branch laws use this restriction.

**Definition 1.18 (Restriction to the original face coordinates).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskRestrict`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskRestrict` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrict an actual disk-set point through the inverse of the current faceCoordinateHomeomorph. Its two inverse identities are consumed by the attachment seam, disk cylinder restriction and time-zero law.

**Theorem 1.19 (Inclusion after restriction).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskIn_restrict`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskIn_restrict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original ambient point is recovered after restricting to its face coordinates and including the disk. This inverse law identifies the representatives in attachment_seam and collar_zero_apply.

**Theorem 1.20 (Restriction after inclusion).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.restrict_diskIn`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.restrict_diskIn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restricting an included disk point recovers that very L2 simplex point. collar_disk_apply uses this identity when evaluating the disk cylinder branch.

**Theorem 1.21 (The actual core and disk cover).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cover`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every point of X is in the literal realized core or in the attached simplex, from the supplied exact union. cylinder_cover and collar_zero_apply consume this cover.

**Theorem 1.22 (Closed core in the original attachment).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.core_closed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.core_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual realized core is closed as the preimage of realization_closed under the unchanged coordinate inclusion. coreCylinder_closed uses it for the ambient closed pasting.

**Theorem 1.23 (Closed attached simplex).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.disk_closed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.disk_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The attached simplex is the finite convex hull of the original ambient coordinate vertices. Its closedness supplies diskCylinder_closed for the ambient pasting.

**Theorem 1.24 (Native boundary and face-coordinate zeros).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.native_boundary_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.native_boundary_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A native proper support omits a face label, giving a zero coordinate. Conversely a zero at i permits support face.erase i; mass one supplies a nonzero coordinate and proves that support nonempty. This avoids inventing a boundary point for a singleton face and is consumed by diskIn_mem_core_iff.

**Theorem 1.25 (The exact full-boundary intersection).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskIn_mem_core_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskIn_mem_core_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original-label disk representative, its inclusion is in P exactly when some face coordinate is zero. The proof uses the literal intersection, a proper nonempty support in face.erase i and the current face-coordinate boundary bridge. It remains valid for singleton faces, whose ordinary full boundary is empty. boundaryToCore and attachment_seam consume this result.

**Definition 1.26 (The original attaching map).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.boundaryToCore`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.boundaryToCore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A boundary disk point is sent into P by its unchanged ambient coordinate vector. The proof uses the exact native intersection and the full-boundary coordinate characterization.

**Theorem 1.27 (The actual attaching seam identity).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.boundaryToCore_in`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.boundaryToCore_in` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Including the native attaching-map value returns exactly the same included disk point. radial_seam consumes this coordinate identity at contraction time zero.

**Definition 1.28 (The face-only radial gauge).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.rho`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.rho` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rho(x)=1-card(face)*min_i(x_i), with the minimum over the original face labels. The gauge is continuous with upper bound one and value one on the full boundary; positivity of the outer denominator comes from the moving seam. No off-face zero is a boundary witness.

**Theorem 1.29 (Continuity of the face radial gauge).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.continuous_rho`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.continuous_rho` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The current continuous_minCoord makes rho=1-card(face)*minCoord continuous. continuous expansion and both radial region closedness proofs consume it.

**Theorem 1.30 (Upper radial bound).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.rho_le_one`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.rho_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shared nonnegative sigma implies rho at most one. expand_one, outerTime, diskCollar_zero and diskCollar_boundary consume this upper bound.

**Theorem 1.31 (Boundary radial value).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.rho_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.rho_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A zero at a face label makes sigma zero and rho one. diskCollar_boundary uses this to identify the outer time with the original time and the projected point with the original boundary point.

**Definition 1.32 (Radial expansion with its literal range proof).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.expand`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.expand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For u>0 and rho(x)<=u, use b+(x-b)/u in the actual L2 simplex. Each coordinate is (u+m*x_i-1)/(m*u), nonnegative by the minimum inequality. Mass one follows by summing the finite uniform coordinates directly: m*(1/m)=1 from cardR_ne, then distributing the affine sum. innerMap and projection consume this construction.

**Theorem 1.33 (Coordinate formula on the literal simplex).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.expand_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.expand_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each expanded coordinate is 1/m+(x_i-1/m)/u. expand_boundary uses this formula at an attained face-coordinate minimum.

**Theorem 1.34 (Unit expansion is identity).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.expand_one`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.expand_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At denominator one, the L2 affine expansion recovers x. diskCollar_zero and diskCollar_boundary consume this identity.

**Theorem 1.35 (Equal positive denominators).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.expand_congr`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.expand_congr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal real denominators produce the same literal expanded point, independently of proof arguments. Both seams and time-zero normalization consume this transport.

**Theorem 1.36 (Attained zero in the projected face).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.expand_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.expand_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

minCoord_attained selects an actual face label. Substituting u=rho=1-m*minCoord into its expanded coordinate gives zero, using m nonzero and rho positive. projection consumes this full-boundary range proof.

**Theorem 1.37 (Continuity with a positive moving denominator).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.continuous_expand`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.continuous_expand` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The L2 affine formula is continuous wherever the supplied denominator is positive. innerMap and projection consume this conditional continuity; no plain-function norm calculation is used.

**Definition 1.38 (The moving radial seam).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cut`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At time s the seam is c_s=1-s/2. It is continuous and lies between one half and one.

**Theorem 1.39 (The moving seam is at least one half).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cut_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cut_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unit-interval time upper bound gives 1/2<=1-s/2. cut_pos and outer_denominator_lower consume it.

**Theorem 1.40 (Positive seam denominator).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cut_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cut_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual attachment and time s in I, cut(s)=1-s/2 is positive from its lower bound one half. expand in innerMap and radial_seam consumes this fact; its lower bound is one half.

**Theorem 1.41 (The seam is at most one).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cut_le_one`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cut_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The time lower bound gives cut(s)<=1. diskCollar_boundary uses it to choose the outer branch on the full disk boundary.

**Theorem 1.42 (Continuous moving seam).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.continuous_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.continuous_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The affine time formula is continuous. Both radial closedness proofs and innerMap consume it.

**Definition 1.43 (Closed inner radial region).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.innerRegion`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.innerRegion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inner cylinder region is rho(x)<=1-s/2. Its range condition is the actual expansion hypothesis of innerMap and diskCollar_inner.

**Definition 1.44 (The closed outer radial region).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outerRegion`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outerRegion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the subset of I times the literal simplex where c_s<=rho(x). The inner region is rho(x)<=c_s; both are closed and cover.

**Theorem 1.45 (Closed inner inequality).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.inner_closed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.inner_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuity of rho and cut makes the inner weak inequality closed. diskCollar consumes this first closed-set proof.

**Theorem 1.46 (Closed outer inequality).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outer_closed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outer_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuity of rho and cut makes the outer weak inequality closed. diskCollar consumes this second closed-set proof.

**Theorem 1.47 (The two radial regions cover).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.radial_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.radial_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Totality of the real order puts every time and disk point in an inner or outer weak-inequality region. diskCollar consumes this cover.

**Definition 1.48 (The central expansion map).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.innerMap`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.innerMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On rho(x)<=cut(s), use diskIn of b+(x-b)/cut(s). The actual simplex nonnegativity and mass-one proofs in expand and its continuity supply a continuous map on this closed region. radial_seam and diskCollar consume it.

**Theorem 1.49 (The projection denominator is at least one half).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outer_denominator_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outer_denominator_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The outer region and cut_lower imply rho>=1/2. outer_rho_pos consumes this quantitative denominator bound.

**Theorem 1.50 (A positive outer projection denominator).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outer_rho_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outer_rho_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lower bound gives rho>0. projection and radial_seam consume this reciprocal-domain proof.

**Definition 1.51 (The actual boundary projection).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.projection`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.projection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On the outer region rho is at least one half. The map sends x to b+(x-b)/rho in the full boundary, with an attained face-coordinate minimum supplying an actual zero coordinate.

**Definition 1.52 (The bounded outer contraction time).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outerTime`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outerTime` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The time is 2*rho(x)-2+s in the unit interval. It is zero on the moving seam and equals s on the disk boundary.

**Definition 1.53 (Contraction of the actual boundary projection).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outerMap`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outerMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At time 2*rho(x)-2+s apply only the supplied standalone contraction of P to boundaryToCore of b+(x-b)/rho(x), then include P in X. radial_seam, diskCollar and its boundary branch consume this map.

**Theorem 1.54 (Equality on the closed moving seam).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.radial_seam`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.radial_seam` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When both radial inequalities hold, rho=cut and outerTime is zero. The supplied contraction at zero is identity; boundaryToCore_in and equal expansion denominators then identify the two actual maps. This is the first seam proof used by diskCollar.

**Definition 1.55 (Closed pasting on the simplex cylinder).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCollar`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCollar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On rho<=c_s use disk inclusion after expansion by c_s; on rho>=c_s use the standalone core contraction of the boundary projection at outerTime. Equality at the seam follows from contraction time zero.

**Theorem 1.56 (Central branch law).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCollar_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCollar_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluate the pasted disk collar on its inner closed set. diskCollar_zero uses this exact formula to establish the initial identity.

**Theorem 1.57 (Outer branch law).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCollar_outer`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCollar_outer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluate the pasted disk collar on its outer closed set. diskCollar_boundary uses it to prove equality with the supplied core contraction.

**Theorem 1.58 (Initial disk identity).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCollar_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCollar_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At time zero cut is one and every point lies in the inner region; expansion at one is identity. collar_zero_apply consumes this disk identity.

**Theorem 1.59 (The entire attaching boundary at every time).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCollar_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCollar_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the full boundary rho=1, projection is the original boundary point and outerTime=s. Thus diskCollar equals the included supplied core contraction. attachment_seam consumes this second gluing boundary law.

**Definition 1.60 (Actual core cylinder).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreCylinder`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreCylinder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cylinder points whose unchanged X-coordinate lies in the realized P. coreCylinderMap and collar use this closed piece.

**Definition 1.61 (Actual disk cylinder).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCylinder`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCylinder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cylinder points whose unchanged X-coordinate lies in the attached ambient faceSimplex. diskCylinderMap and collar use this closed piece.

**Theorem 1.62 (Closed core cylinder).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreCylinder_closed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreCylinder_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pull back core_closed along the cylinder second projection. collar consumes this closedness proof.

**Theorem 1.63 (Closed disk cylinder).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCylinder_closed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCylinder_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pull back disk_closed along the cylinder second projection. collar consumes this closedness proof.

**Theorem 1.64 (Cover of the actual X cylinder).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cylinder_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cylinder_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the literal attachment cover to the second coordinate. collar consumes this cover.

**Definition 1.65 (The supplied contraction on the actual core).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreCylinderMap`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreCylinderMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrict the unchanged ambient core point to Space P, apply A.contraction at the same time and include it in X. attachment_seam and collar use this map.

**Definition 1.66 (The disk collar in ambient coordinates).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCylinderMap`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCylinderMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrict an actual disk-set point to its L2 face coordinates and evaluate diskCollar. attachment_seam and collar use this map.

**Theorem 1.67 (Equality on the literal core-disk intersection).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.attachment_seam`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.attachment_seam` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Recover the disk representative by diskIn_restrict. The exact intersection theorem gives its full-boundary witness; diskCollar_boundary then equals the same supplied core contraction on the same coordinate vector. collar consumes this second closed-cover seam.

**Definition 1.68 (Closed pasting on the actual attachment cylinder).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The core piece is the supplied contraction followed by inclusion, and the disk piece is diskCollar. The exact intersection is the full boundary, where both pieces equal the same core contraction at time s. Closed-cover pasting proves continuity on I times the actual realization of X.

**Theorem 1.69 (Core branch law).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_core_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_core_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ambient closed pasting evaluates to the included supplied contraction on every actual core point. The endpoint, core-preservation, initial and based fixed-point proofs consume this law.

**Theorem 1.70 (Disk branch law).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_disk_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_disk_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ambient collar evaluates to diskCollar on each included disk representative, using restrict_diskIn. collar_zero_apply consumes this branch law.

**Theorem 1.71 (Initial identity on all of X).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_zero_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_zero_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the actual core-disk cover, the supplied contraction at zero and diskCollar_zero to prove collar(0,x)=x. Both based homotopies consume it.

**Theorem 1.72 (The endpoint collapses the entire core).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_core_one`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_core_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At time one the supplied contraction sends every core point to p, so the ambient collar sends it to the actual included p. quotientInverse consumes this quotient descent condition.

**Theorem 1.73 (The whole homotopy preserves P).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_preserves_core`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_preserves_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every time a core point remains the included value of the contraction on P. quotient_collar_respects consumes this full-time condition.

**Theorem 1.74 (The actual included point stays fixed).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The supplied contraction is relative to p; the ambient collar therefore fixes coreIn(p) at every time. collarHomotopy, quotientHomotopy and quotientEquivalence consume this based law.

**Definition 1.75 (The literal core collapse).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.Q`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q is the existing subset collapse of coreSet in the actual realization of X, with its native quotient topology.

**Definition 1.76 (The unchanged quotient map).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.q`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

q is exactly the existing canonical collapseMap of coreSet. It is not changed by a basepoint-adjustment construction.

**Definition 1.77 (The endpoint collar descends).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientInverse`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientInverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse Q to X is Quotient.lift of x mapped to collar(1,x). The endpoint sends every core point to the same included p, and quotient-lift continuity follows from the actual continuous collar.

**Definition 1.78 (The first based homotopy from this collar).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collarHomotopy`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collarHomotopy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the actual collar as a homotopy from identity on X to quotientInverse after the literal q. Its singleton relative condition is collar_fixed at the actual included p. quotientEquivalence uses its reversal.

**Theorem 1.79 (Full-time quotient descent).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotient_collar_respects`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotient_collar_respects` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of representatives is preserved; two actual core representatives remain in the core at every time and hence have the same q-class. quotientCollar consumes this descent proof.

**Definition 1.80 (The descended actual collar).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientCollar`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientCollar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every time descend the map x sent to q(collar(s,x)) through the actual core subset setoid. quotientHomotopy uses exactly this function.

**Definition 1.81 (The second based homotopy on the quotient).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientHomotopy`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientHomotopy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual descended collar runs from identity on Q to q after quotientInverse and fixes q(coreIn(p)). Continuous time descent uses continuous_lift_prod_right for locally compact I. quotientEquivalence uses its reversal.

**Definition 1.82 (Both based inverse homotopies for the actual q).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientEquivalence`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientEquivalence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward map is literally collapseMap(coreSet) and the backward map is Quotient.lift of collar(1,-). The X homotopy uses the very collar; the Q homotopy descends q after that collar using preservation of P. Both fix the actual included p or its q-class, and both are reversed to fit BasedEquivalence. This construction assumes only the based contraction of P, never a contraction of X, a sphere comparison or freeness in X.

## References

- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.Attachment`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.BDisk`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.Disk`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.Q`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.attachment_seam`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.basepoint`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.boundaryToCore`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.boundaryToCore_in`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collarHomotopy`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_core_apply`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_core_one`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_disk_apply`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_fixed`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_preserves_core`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_zero_apply`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.continuous_cut`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.continuous_expand`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.continuous_rho`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreCylinder`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreCylinderMap`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreCylinder_closed`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreIn`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreRestrict`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreSet`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.core_closed`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.core_le`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cover`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cut`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cut_le_one`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cut_lower`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cut_pos`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cylinder_cover`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCollar`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCollar_boundary`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCollar_inner`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCollar_outer`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCollar_zero`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCylinder`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCylinderMap`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCylinder_closed`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskIn`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskIn_mem_core_iff`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskIn_restrict`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskRestrict`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskSet`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.disk_closed`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.disk_mem`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.expand`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.expand_boundary`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.expand_congr`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.expand_coordinate`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.expand_one`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.faceInhabited`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.innerMap`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.innerRegion`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.inner_closed`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.native_boundary_iff`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outerMap`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outerRegion`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outerTime`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outer_closed`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outer_denominator_lower`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outer_rho_pos`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.pasteClosed`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.pasteClosed_left`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.pasteClosed_right`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.projection`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.q`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientCollar`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientEquivalence`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientHomotopy`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientInverse`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotient_collar_respects`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.radial_cover`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.radial_seam`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.restrict_diskIn`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.rho`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.rho_boundary`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.rho_le_one`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.simplex_le`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.simplex_realization`
- Dependency: [D5/S3/Geometry/FiniteAlexanderDualCollapse](../FiniteAlexanderDualCollapse.md)
- Dependency: [D5/S3/Geometry/FiniteSimplexBoundarySphere](../FiniteSimplexBoundarySphere.md)
