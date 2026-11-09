# Rewiring away from selected vertices and Fano minimality

## Abstract

Rewiring away from selected vertices and Fano minimality

Rewiring edges whose endpoints are both outside the fixed selection preserves formation for every smaller selection and therefore inclusion-minimality. The actual fourteen-vertex Fano adjacency table, eight-set and all deletion witnesses are retained with the original cyclic labels. This module proves simplicity, cubic neighbor lists and minimality of that selection; graph invariant upper maxima are established in HeawoodParameters.

**Theorem 1.1 (forms rewiring).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.forms_rewiring`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.forms_rewiring` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem forms_rewiring {Vertex : Type} (original modified : Vertex → Vertex → Prop) (selection smaller : Vertex → Prop) (hsubset : ∀ vertex, smaller vertex → selection vertex) (hagreement : ∀ first second, selection first ∨ selection second → (original first second ↔ modified first second)) (hforms : Forms original smaller) : Forms modified smaller.

**Theorem 1.2 (minimal rewiring forward).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.minimal_rewiring_forward`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.minimal_rewiring_forward` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem minimal_rewiring_forward {Vertex : Type} (original modified : Vertex → Vertex → Prop) (selection : Vertex → Prop) (hagreement : ∀ first second, selection first ∨ selection second → (original first second ↔ modified first second)) (hminimal : Minimal original selection) : Minimal modified selection.

**Theorem 1.3 (minimal rewiring).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.minimal_rewiring`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.minimal_rewiring` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem minimal_rewiring {Vertex : Type} (original modified : Vertex → Vertex → Prop) (selection : Vertex → Prop) (hagreement : ∀ first second, selection first ∨ selection second → (original first second ↔ modified first second)) : Minimal original selection ↔ Minimal modified selection.

**Definition 1.4 (fanoNeighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fanoNeighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fanoNeighbors` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def fanoNeighbors (vertex : Fin 14) : List (Fin 14).

**Definition 1.5 (FanoAdj).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.FanoAdj`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.FanoAdj` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def FanoAdj (first second : Fin 14) : Prop.

**Definition 1.6 (fanoSelected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fanoSelected`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fanoSelected` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def fanoSelected (vertex : Fin 14) : Prop.

**Definition 1.7 (fanoFailure).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fanoFailure`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fanoFailure` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def fanoFailure (vertex : Fin 14) : Fin 14.

**Theorem 1.8 (fano simple cubic).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fano_simple_cubic`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fano_simple_cubic` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem fano_simple_cubic : (∀ vertex : Fin 14, ¬ FanoAdj vertex vertex) ∧ (∀ first second : Fin 14, FanoAdj first second ↔ FanoAdj second first) ∧ (∀ vertex : Fin 14, (fanoNeighbors vertex).length = 3 ∧ (fanoNeighbors vertex).Nodup).

**Theorem 1.9 (fano forms).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fano_forms`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fano_forms` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem fano_forms : Forms FanoAdj fanoSelected.

**Theorem 1.10 (fano deletion failures).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fano_deletion_failures`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fano_deletion_failures` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem fano_deletion_failures : ∀ deleted : Fin 14, fanoSelected deleted → ¬ (fanoSelected (fanoFailure deleted) ∧ fanoFailure deleted ≠ deleted) ∧ ¬ TwoAt FanoAdj (fun vertex => fanoSelected vertex ∧ vertex ≠ deleted) (fanoFailure deleted).

**Theorem 1.11 (fano minimal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fano_minimal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fano_minimal` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem fano_minimal : Minimal FanoAdj fanoSelected.

**Theorem 1.12 (fano selected card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fano_selected_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fano_selected_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem fano_selected_card : ((List.finRange 14).filter (fun vertex => decide (fanoSelected vertex))).length = 8.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.FanoAdj`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fanoFailure`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fanoNeighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fanoSelected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fano_deletion_failures`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fano_forms`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fano_minimal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fano_selected_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.fano_simple_cubic`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.forms_rewiring`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.minimal_rewiring`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.minimal_rewiring_forward`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate](SubcubicCertificate.md)
