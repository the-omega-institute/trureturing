# Safe certificates under neighborhood covers

## Abstract

Safe certificates under neighborhood covers

A NeighborhoodCover preserves edges and is bijective on each lifted neighborhood. It does not assert global surjectivity. Safe certificates prevent the triangle collision that can destroy a lifted star after one selected deletion. They imply minimal pullback for simple symmetric graphs. Boundary triangle-freeness suffices, and ordinary triangle-freeness is a further sufficient hypothesis. The entire local certificate telescope is retained.

**Definition 1.1 (TriangleFree).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.TriangleFree`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.TriangleFree` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def TriangleFree {Vertex : Type} (adjacency : Vertex → Vertex → Prop) : Prop.

**Definition 1.2 (SafeFailure).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.SafeFailure`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.SafeFailure` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def SafeFailure {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (deleted outside : Vertex) : Prop.

**Definition 1.3 (HasSafeCertificates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.HasSafeCertificates`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.HasSafeCertificates` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def HasSafeCertificates {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) : Prop.

**Definition 1.4 (BoundaryTriangleFree).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.BoundaryTriangleFree`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.BoundaryTriangleFree` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def BoundaryTriangleFree {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) : Prop.

**Definition 1.5 (NeighborhoodCover).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.NeighborhoodCover`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.NeighborhoodCover` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: structure NeighborhoodCover {Base Lift : Type} (baseAdjacency : Base → Base → Prop) (liftAdjacency : Lift → Lift → Prop) (projection : Lift → Base) : Prop.

**Theorem 1.6 (twoAt mono).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.twoAt_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.twoAt_mono` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem twoAt_mono {Vertex : Type} {adjacency : Vertex → Vertex → Prop} {smaller larger : Vertex → Prop} {outside : Vertex} (hinclusion : ∀ vertex, smaller vertex → larger vertex) (hstar : TwoAt adjacency smaller outside) : TwoAt adjacency larger outside.

**Theorem 1.7 (forms mono).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.forms_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.forms_mono` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem forms_mono {Vertex : Type} {adjacency : Vertex → Vertex → Prop} {smaller larger : Vertex → Prop} (hinclusion : ∀ vertex, smaller vertex → larger vertex) (hforms : Forms adjacency smaller) : Forms adjacency larger.

**Theorem 1.8 (minimal of single deletions).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.minimal_of_single_deletions`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.minimal_of_single_deletions` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem minimal_of_single_deletions {Vertex : Type} {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop} (hforms : Forms adjacency selection) (hdeletions : ∀ deleted, selection deleted → ¬ Forms adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted)) : Minimal adjacency selection.

**Theorem 1.9 (twoAt pullback).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.twoAt_pullback`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.twoAt_pullback` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem twoAt_pullback {Base Lift : Type} {baseAdjacency : Base → Base → Prop} {liftAdjacency : Lift → Lift → Prop} {projection : Lift → Base} (cover : NeighborhoodCover baseAdjacency liftAdjacency projection) {selection : Base → Prop} (outside : Lift) (hstar : TwoAt baseAdjacency selection (projection outside)) : TwoAt liftAdjacency (fun vertex => selection (projection vertex)) outside.

**Theorem 1.10 (forms pullback).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.forms_pullback`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.forms_pullback` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem forms_pullback {Base Lift : Type} {baseAdjacency : Base → Base → Prop} {liftAdjacency : Lift → Lift → Prop} {projection : Lift → Base} (cover : NeighborhoodCover baseAdjacency liftAdjacency projection) {selection : Base → Prop} (hforms : Forms baseAdjacency selection) : Forms liftAdjacency (fun vertex => selection (projection vertex)).

**Theorem 1.11 (self deletion projects).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.self_deletion_projects`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.self_deletion_projects` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem self_deletion_projects {Base Lift : Type} {baseAdjacency : Base → Base → Prop} {liftAdjacency : Lift → Lift → Prop} {projection : Lift → Base} (cover : NeighborhoodCover baseAdjacency liftAdjacency projection) (hirreflexive : ∀ vertex, ¬ baseAdjacency vertex vertex) (hsymmetric : ∀ first second, liftAdjacency first second → liftAdjacency second first) {selection : Base → Prop} (deleted : Lift) (hstar : TwoAt liftAdjacency (fun vertex => selection (projection vertex) ∧ vertex ≠ deleted) deleted) : TwoAt baseAdjacency (fun vertex => selection vertex ∧ vertex ≠ projection deleted) (projection deleted).

**Theorem 1.12 (adjacent deletion projects).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.adjacent_deletion_projects`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.adjacent_deletion_projects` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem adjacent_deletion_projects {Base Lift : Type} {baseAdjacency : Base → Base → Prop} {liftAdjacency : Lift → Lift → Prop} {projection : Lift → Base} (cover : NeighborhoodCover baseAdjacency liftAdjacency projection) {selection : Base → Prop} (deleted outside : Lift) (hadjacent : liftAdjacency outside deleted) (hsafe : ∀ center, selection center → baseAdjacency (projection outside) center → ¬ baseAdjacency center (projection deleted)) (hstar : TwoAt liftAdjacency (fun vertex => selection (projection vertex) ∧ vertex ≠ deleted) outside) : TwoAt baseAdjacency (fun vertex => selection vertex ∧ vertex ≠ projection deleted) (projection outside).

**Theorem 1.13 (nonadjacent failure private path).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.nonadjacent_failure_private_path`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.nonadjacent_failure_private_path` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem nonadjacent_failure_private_path {Vertex : Type} {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop} (hforms : Forms adjacency selection) (deleted outside : Vertex) (hfailure : Failure adjacency selection deleted outside) (hnonadjacent : ¬ adjacency outside deleted) : ∃ support, selection support ∧ adjacency outside support ∧ adjacency support deleted ∧ (∀ neighbor, selection neighbor → adjacency outside neighbor → neighbor = support) ∧ (∀ neighbor, selection neighbor → adjacency support neighbor → neighbor = deleted).

**Theorem 1.14 (private path deletion fails).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.private_path_deletion_fails`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.private_path_deletion_fails` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem private_path_deletion_fails {Base Lift : Type} {baseAdjacency : Base → Base → Prop} {liftAdjacency : Lift → Lift → Prop} {projection : Lift → Base} (cover : NeighborhoodCover baseAdjacency liftAdjacency projection) {selection : Base → Prop} (deleted support outside : Lift) (houtside : ¬ selection (projection outside)) (houtsideSupport : liftAdjacency outside support) (hsupportDeleted : liftAdjacency support deleted) (huniqueOutside : ∀ neighbor, selection neighbor → baseAdjacency (projection outside) neighbor → neighbor = projection support) (huniqueSupport : ∀ neighbor, selection neighbor → baseAdjacency (projection support) neighbor → neighbor = projection deleted) : ¬ Forms liftAdjacency (fun vertex => selection (projection vertex) ∧ vertex ≠ deleted).

**Theorem 1.15 (minimal pullback of safe certificates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.minimal_pullback_of_safe_certificates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.minimal_pullback_of_safe_certificates` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem minimal_pullback_of_safe_certificates {Base Lift : Type} {baseAdjacency : Base → Base → Prop} {liftAdjacency : Lift → Lift → Prop} {projection : Lift → Base} (cover : NeighborhoodCover baseAdjacency liftAdjacency projection) (hirreflexive : ∀ vertex, ¬ baseAdjacency vertex vertex) (hbaseSymmetric : ∀ first second, baseAdjacency first second → baseAdjacency second first) (hliftSymmetric : ∀ first second, liftAdjacency first second → liftAdjacency second first) {selection : Base → Prop} (hforms : Forms baseAdjacency selection) (hcertificates : HasSafeCertificates baseAdjacency selection) : Minimal liftAdjacency (fun vertex => selection (projection vertex)).

**Theorem 1.16 (safe certificates of boundary triangle free).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.safe_certificates_of_boundary_triangle_free`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.safe_certificates_of_boundary_triangle_free` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem safe_certificates_of_boundary_triangle_free {Vertex : Type} {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop} (hminimal : Minimal adjacency selection) (hboundary : BoundaryTriangleFree adjacency selection) : HasSafeCertificates adjacency selection.

**Theorem 1.17 (minimal pullback of boundary triangle free).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.minimal_pullback_of_boundary_triangle_free`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.minimal_pullback_of_boundary_triangle_free` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem minimal_pullback_of_boundary_triangle_free {Base Lift : Type} {baseAdjacency : Base → Base → Prop} {liftAdjacency : Lift → Lift → Prop} {projection : Lift → Base} (cover : NeighborhoodCover baseAdjacency liftAdjacency projection) (hirreflexive : ∀ vertex, ¬ baseAdjacency vertex vertex) (hbaseSymmetric : ∀ first second, baseAdjacency first second → baseAdjacency second first) (hliftSymmetric : ∀ first second, liftAdjacency first second → liftAdjacency second first) {selection : Base → Prop} (hminimal : Minimal baseAdjacency selection) (hboundary : BoundaryTriangleFree baseAdjacency selection) : Minimal liftAdjacency (fun vertex => selection (projection vertex)).

**Theorem 1.18 (minimal pullback).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.minimal_pullback`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.minimal_pullback` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem minimal_pullback {Base Lift : Type} {baseAdjacency : Base → Base → Prop} {liftAdjacency : Lift → Lift → Prop} {projection : Lift → Base} (cover : NeighborhoodCover baseAdjacency liftAdjacency projection) (hirreflexive : ∀ vertex, ¬ baseAdjacency vertex vertex) (hbaseSymmetric : ∀ first second, baseAdjacency first second → baseAdjacency second first) (hliftSymmetric : ∀ first second, liftAdjacency first second → liftAdjacency second first) (htriangleFree : TriangleFree baseAdjacency) {selection : Base → Prop} (hminimal : Minimal baseAdjacency selection) : Minimal liftAdjacency (fun vertex => selection (projection vertex)).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.BoundaryTriangleFree`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.HasSafeCertificates`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.NeighborhoodCover`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.SafeFailure`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.TriangleFree`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.adjacent_deletion_projects`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.forms_mono`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.forms_pullback`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.minimal_of_single_deletions`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.minimal_pullback`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.minimal_pullback_of_boundary_triangle_free`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.minimal_pullback_of_safe_certificates`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.nonadjacent_failure_private_path`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.private_path_deletion_fails`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.safe_certificates_of_boundary_triangle_free`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.self_deletion_projects`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.twoAt_mono`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverPullback.twoAt_pullback`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/RegularBound](RegularBound.md)
