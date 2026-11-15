# The exact test for cover-stable minimality

## Abstract

The exact test for cover-stable minimality

For each selected deletion, the canonical two-sheeted cover crosses precisely the edges from that vertex to originally unselected vertices. A missing safe certificate makes the lifted selection nonminimal. For a minimal selection in a simple symmetric graph, safe certificates are equivalent to minimality in all its canonical test covers and to preservation in every neighborhood cover. These statements require no global projection-surjectivity convention. They do not by themselves prove the connected-countercover strengthening.

**Definition 1.1 (Crossed).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverStability.Crossed`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CoverStability.Crossed` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def Crossed {Vertex : Type} (selection : Vertex → Prop) (deleted first second : Vertex) : Prop.

**Definition 1.2 (CanonicalAdj).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverStability.CanonicalAdj`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CoverStability.CanonicalAdj` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def CanonicalAdj {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (deleted : Vertex) (first second : Vertex × Bool) : Prop.

**Theorem 1.3 (canonical symmetric).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverStability.canonical_symmetric`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverStability.canonical_symmetric` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem canonical_symmetric {Vertex : Type} {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop} (deleted : Vertex) (hsymmetric : ∀ first second, adjacency first second → adjacency second first) : ∀ first second, CanonicalAdj adjacency selection deleted first second → CanonicalAdj adjacency selection deleted second first.

**Theorem 1.4 (canonical cover).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverStability.canonical_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverStability.canonical_cover` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem canonical_cover {Vertex : Type} {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop} (deleted : Vertex) : NeighborhoodCover adjacency (CanonicalAdj adjacency selection deleted) Prod.fst.

**Theorem 1.5 (canonical selected edge).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverStability.canonical_selected_edge`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverStability.canonical_selected_edge` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem canonical_selected_edge {Vertex : Type} {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop} (deleted first second : Vertex) (sheet : Bool) (hfirst : selection first) (hsecond : selection second) (hedge : adjacency first second) : CanonicalAdj adjacency selection deleted (first, sheet) (second, sheet).

**Theorem 1.6 (canonical retained edge).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverStability.canonical_retained_edge`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverStability.canonical_retained_edge` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem canonical_retained_edge {Vertex : Type} {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop} (deleted outside selected : Vertex) (sheet : Bool) (hselected : selection selected) (hdifferent : selected ≠ deleted) (hedge : adjacency outside selected) : CanonicalAdj adjacency selection deleted (outside, sheet) (selected, sheet).

**Theorem 1.7 (twoAt canonical after deletion).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverStability.twoAt_canonical_after_deletion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverStability.twoAt_canonical_after_deletion` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem twoAt_canonical_after_deletion {Vertex : Type} {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop} (deleted outside : Vertex) (sheet : Bool) (hstar : TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) outside) : TwoAt (CanonicalAdj adjacency selection deleted) (fun vertex => selection vertex.1 ∧ vertex ≠ (deleted, false)) (outside, sheet).

**Theorem 1.8 (canonical deletion forms of missing certificate).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverStability.canonical_deletion_forms_of_missing_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverStability.canonical_deletion_forms_of_missing_certificate` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem canonical_deletion_forms_of_missing_certificate {Vertex : Type} {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop} (hirreflexive : ∀ vertex, ¬ adjacency vertex vertex) (hsymmetric : ∀ first second, adjacency first second → adjacency second first) (deleted : Vertex) (hselected : selection deleted) (hmissing : ¬ ((¬ TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) deleted) ∨ ∃ outside, SafeFailure adjacency selection deleted outside)) : Forms (CanonicalAdj adjacency selection deleted) (fun vertex => selection vertex.1 ∧ vertex ≠ (deleted, false)).

**Theorem 1.9 (canonical nonminimal of missing certificate).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverStability.canonical_nonminimal_of_missing_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverStability.canonical_nonminimal_of_missing_certificate` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem canonical_nonminimal_of_missing_certificate {Vertex : Type} {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop} (hirreflexive : ∀ vertex, ¬ adjacency vertex vertex) (hsymmetric : ∀ first second, adjacency first second → adjacency second first) (deleted : Vertex) (hselected : selection deleted) (hmissing : ¬ ((¬ TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) deleted) ∨ ∃ outside, SafeFailure adjacency selection deleted outside)) : ¬ Minimal (CanonicalAdj adjacency selection deleted) (fun vertex => selection vertex.1).

**Theorem 1.10 (safe certificates iff canonical minimal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverStability.safe_certificates_iff_canonical_minimal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverStability.safe_certificates_iff_canonical_minimal` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem safe_certificates_iff_canonical_minimal {Vertex : Type} {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop} (hirreflexive : ∀ vertex, ¬ adjacency vertex vertex) (hsymmetric : ∀ first second, adjacency first second → adjacency second first) (hminimal : Minimal adjacency selection) : HasSafeCertificates adjacency selection ↔ ∀ deleted, selection deleted → Minimal (CanonicalAdj adjacency selection deleted) (fun vertex => selection vertex.1).

**Theorem 1.11 (safe certificates iff all covers).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverStability.safe_certificates_iff_all_covers`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverStability.safe_certificates_iff_all_covers` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem safe_certificates_iff_all_covers {Vertex : Type} {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop} (hirreflexive : ∀ vertex, ¬ adjacency vertex vertex) (hsymmetric : ∀ first second, adjacency first second → adjacency second first) (hminimal : Minimal adjacency selection) : HasSafeCertificates adjacency selection ↔ ∀ (Lift : Type) (liftAdjacency : Lift → Lift → Prop) (projection : Lift → Vertex), NeighborhoodCover adjacency liftAdjacency projection → (∀ first second, liftAdjacency first second → liftAdjacency second first) → Minimal liftAdjacency (fun vertex => selection (projection vertex)).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverStability.CanonicalAdj`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverStability.Crossed`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverStability.canonical_cover`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverStability.canonical_deletion_forms_of_missing_certificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverStability.canonical_nonminimal_of_missing_certificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverStability.canonical_retained_edge`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverStability.canonical_selected_edge`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverStability.canonical_symmetric`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverStability.safe_certificates_iff_all_covers`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverStability.safe_certificates_iff_canonical_minimal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverStability.twoAt_canonical_after_deletion`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CoverPullback](CoverPullback.md)
