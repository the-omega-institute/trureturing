# The actual ambient ten-vertex core cap

## Abstract

The actual ambient ten-vertex core cap

The complete 1024-mask dense-core certificate feeds a generic supported-deletion proof in an arbitrary ambient relation. The embedding is injective and induced; only core labels three and eleven may acquire neighbors outside the embedded core. These exact neighborhood hypotheses are preserved. Every minimal selection has at most six core vertices. Actual coverage of the remaining two ports gives SF two exactly eight for the original twelve-vertex graph. Shared-port cyclic identifications, connectivity, exact edge counts and the other invariants of J_r are separate obligations.

**Theorem 1.1 (supported deletion).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.supported_deletion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.supported_deletion` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem supported_deletion {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (deleted : Vertex) (hforms : Forms adjacency selection) (hnew : TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) deleted) (hadjacent : ∀ outside, ¬ selection outside → adjacency outside deleted → TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) outside) (hreplacement : ∀ center, selection center → adjacency center deleted → ∃ leaf, (selection leaf ∧ leaf ≠ deleted) ∧ adjacency center leaf) : Forms adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted).

**Definition 1.2 (coreLabel).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.coreLabel`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.coreLabel` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def coreLabel (vertex : Fin 10) : Fin 12.

**Definition 1.3 (CoreAdj).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.CoreAdj`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.CoreAdj` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def CoreAdj (first second : Fin 10) : Prop.

**Definition 1.4 (attachment).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.attachment`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.attachment` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def attachment (vertex : Fin 10) : Prop.

**Definition 1.5 (coreSelected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.coreSelected`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.coreSelected` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def coreSelected (mask : Fin 1024) (vertex : Fin 10) : Prop.

**Definition 1.6 (coreCard).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.coreCard`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.coreCard` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def coreCard (mask : Fin 1024) : Nat.

**Definition 1.7 (SafeCore).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.SafeCore`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.SafeCore` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def SafeCore (mask : Fin 1024) (deleted : Fin 10) : Prop.

**Theorem 1.8 (dense core certificate).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.dense_core_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.dense_core_certificate` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_core_certificate : ∀ mask : Fin 1024, 7 ≤ coreCard mask → ∃ deleted, SafeCore mask deleted.

**Theorem 1.9 (lift core star).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.lift_core_star`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.lift_core_star` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem lift_core_star {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (embedding : Fin 10 → Vertex) (mask : Fin 1024) (hinjective : ∀ first second, embedding first = embedding second → first = second) (hedges : ∀ first second, adjacency (embedding first) (embedding second) ↔ CoreAdj first second) (hselection : ∀ vertex, selection (embedding vertex) ↔ coreSelected mask vertex) (deleted outside : Fin 10) (hstar : TwoAt CoreAdj (fun vertex => coreSelected mask vertex ∧ vertex ≠ deleted) outside) : TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ embedding deleted) (embedding outside).

**Theorem 1.10 (ambient core cap).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.ambient_core_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.ambient_core_cap` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem ambient_core_cap {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (embedding : Fin 10 → Vertex) (mask : Fin 1024) (hsymmetric : ∀ first second, adjacency first second → adjacency second first) (hinjective : ∀ first second, embedding first = embedding second → first = second) (hedges : ∀ first second, adjacency (embedding first) (embedding second) ↔ CoreAdj first second) (hselection : ∀ vertex, selection (embedding vertex) ↔ coreSelected mask vertex) (hclosed : ∀ vertex, ¬ attachment vertex → ∀ outside, adjacency (embedding vertex) outside → ∃ other, outside = embedding other) (hminimal : Minimal adjacency selection) : coreCard mask ≤ 6.

**Theorem 1.11 (core label properties).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.core_label_properties`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.core_label_properties` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem core_label_properties : Function.Injective coreLabel ∧ (∀ w : Fin 12, w = 0 ∨ w = 6 ∨ ∃ v : Fin 10, coreLabel v = w) ∧ (∀ v : Fin 10, ¬ attachment v → ∀ w : Fin 12, Adj (coreLabel v) w → ∃ other, w = coreLabel other).

**Theorem 1.12 (minimal card bound).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.minimal_card_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.minimal_card_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem minimal_card_bound (S : Finset (Fin 12)) (hS : IsMinimalStarForming graph 2 S) : S.card ≤ 8.

**Theorem 1.13 (sf graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.sf_graph`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.sf_graph` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem sf_graph : SF graph 2 = 8.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.CoreAdj`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.SafeCore`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.ambient_core_cap`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.attachment`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.coreCard`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.coreLabel`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.coreSelected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.core_label_properties`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.dense_core_certificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.lift_core_star`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.minimal_card_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.sf_graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.supported_deletion`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate](SubcubicCertificate.md)
