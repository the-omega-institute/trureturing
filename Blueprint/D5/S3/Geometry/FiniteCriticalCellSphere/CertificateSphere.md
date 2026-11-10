# The finite certificate on the original K

## Abstract

The computed finite Alexander certificate supplies the original-K based sphere maps and retained-label equations.

These constructions consume the current finite Alexander certificate and the attachment sphere construction. They retain literal j, original ambient labels, the whole retained endpoint and both based inverse homotopies. Availability for unrestricted arbitrary-plane-H original-K inputs remains open.

**Definition 1.1 (Computing every attachment input).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.attachment`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.attachment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the exact frozen AlexanderDual Certificate, use X=c.X, P=c.P, face=c.lambda, the included original apex c.a, c.cell_decomposition, c.cell_intersection, c.arithmetic and the already computed standalone c.pContraction. No desired collar or sphere outcome is added to Certificate.

**Definition 1.2 (The original apex in K).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.apex`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.apex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Include the original cone point a into the original realization of K by the existing actual coordinate inclusion.

**Definition 1.3 (The computed original reduction).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.reductionEquivalence`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.reductionEquivalence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use c.reductionSDR.retraction from K to X and c.reduction.inclusion from X to K. The whole-endpoint SDR supplies the left inverse homotopy; the exact retraction-inclusion identity supplies the right one. Both fix the original apex.

**Definition 1.4 (The sphere point for the original certificate).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.spherePoint`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.spherePoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the actual attachment sphere basepoint in the exact existing StdSphere(c.d), with c.d=lambda.card-1.

**Definition 1.5 (The actual original-K based sphere endpoint).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.sphereEquivalence`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.sphereEquivalence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose the computed original reduction based equivalence with the actual attachment sphere equivalence. The output is a BasedEquivalence between the original realization of c.K and the existing EuclideanSphereJoin.StdSphere(c.d), including both genuine inverse homotopies.

**Theorem 1.6 (Original maps with computed reduction operands).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.sphere_maps`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.sphere_maps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward is sphereHomeomorph after q after c.reductionSDR.retraction. The backward is c.reduction.inclusion after quotientInverse after sphereHomeomorph inverse. All operands come from the existing owners or the actual collar construction.

**Theorem 1.7 (Original disk representatives retain rational Psi).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.sphere_representative`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.sphere_representative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For lambda.card>=2 and any literal complementary simplex point, the original K sphere map on its existing reduction inclusion equals the same exact rational spherePsi representative.

**Theorem 1.8 (Original barycenter and boundary equations).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.sphere_poles`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.sphere_poles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For lambda.card>=2, the actual barycenter included into the original K maps to the reindexed north pole; every full-boundary representative maps to the reindexed south pole.

**Theorem 1.9 (Both original pointwise based homotopies).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.sphere_based_laws`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.sphere_based_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward and backward send the original included apex and actual sphere point to each other. At every time the original-K inverse homotopy fixes the apex and the sphere inverse homotopy fixes the actual sphere point.

**Theorem 1.10 (The entire retained endpoint stays fixed).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.reduction_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.reduction_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual x in c.X and every time, the original computed reductionSDR homotopy fixes c.reduction.inclusion(x). This preserves whole-endpoint fixedness, not only the apex.

**Theorem 1.11 (Original-K disk coordinates and ambient labels).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.disk_original_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.disk_original_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After the literal disk inclusion and existing reduction inclusion into K, each original lambda coordinate equals the input coordinate and every original label outside lambda is zero.

**Theorem 1.12 (True original ambient ghosts stay zero).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.ambient_ghost`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.ambient_ghost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual K point and every original label outside insert(a,W), that coordinate is zero. Thus all actual K-valued inverse and homotopy outputs retain these ghosts. A label outside lambda that is an actual core vertex is not incorrectly called a ghost.

**Definition 1.13 (The unchanged original j).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.originalAttachingMap`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.originalAttachingMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is exactly c.j from the actual realization of D dual to the actual realization of E dual. No null or zero map is substituted and no homotopy equivalence of j is inferred.

## References

- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.ambient_ghost`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.apex`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.attachment`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.disk_original_coordinates`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.originalAttachingMap`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.reductionEquivalence`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.reduction_fixed`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.sphereEquivalence`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.spherePoint`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.sphere_based_laws`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.sphere_maps`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.sphere_poles`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.sphere_representative`
- Dependency: [D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere](AttachmentSphere.md)
