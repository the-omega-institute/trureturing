# The original subcubic block and forced-certificate collision

## Abstract

The original subcubic block and forced-certificate collision

The original twelve-vertex graph, ports zero and six, selection of size eight, deletion failures, forced witnesses and simultaneous replacement collision are retained. The complete 4096-mask port-state caps are transported to every actual canonical dissociation subset, giving beta two exactly seven with an attaining port-state witness. The displayed selection is minimal. Both bipartiteness and maximum degree three are checked. The refutation addresses universal subcubic bipartite identification and simultaneous replacement by the two forced certificates. It does not assert the cyclic shared-port family parameters or planarity results.

**Theorem 1.1 (minimal of deletion failures).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.minimal_of_deletion_failures`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.minimal_of_deletion_failures` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem minimal_of_deletion_failures {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (hforms : Forms adjacency selection) (hfail : ∀ deleted, selection deleted → ∃ outside, ¬ (selection outside ∧ outside ≠ deleted) ∧ ¬ TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) outside) : Minimal adjacency selection.

**Definition 1.2 (neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.neighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.neighbors` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def neighbors (vertex : Fin 12) : List (Fin 12).

**Definition 1.3 (Adj).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.Adj`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.Adj` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def Adj (first second : Fin 12) : Prop.

**Definition 1.4 (selected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.selected`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.selected` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def selected (vertex : Fin 12) : Prop.

**Definition 1.5 (failure).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.failure`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.failure` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def failure (vertex : Fin 12) : Fin 12.

**Theorem 1.6 (adjacency simple).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.adjacency_simple`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.adjacency_simple` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem adjacency_simple : (∀ vertex : Fin 12, ¬ Adj vertex vertex) ∧ (∀ first second : Fin 12, Adj first second ↔ Adj second first).

**Theorem 1.7 (base forms).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.base_forms`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.base_forms` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem base_forms : Forms Adj selected.

**Theorem 1.8 (base deletion failures).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.base_deletion_failures`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.base_deletion_failures` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem base_deletion_failures : ∀ deleted : Fin 12, selected deleted → ¬ (selected (failure deleted) ∧ failure deleted ≠ deleted) ∧ ¬ TwoAt Adj (fun vertex => selected vertex ∧ vertex ≠ deleted) (failure deleted).

**Theorem 1.9 (base minimal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.base_minimal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.base_minimal` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem base_minimal : Minimal Adj selected.

**Theorem 1.10 (forced certificates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.forced_certificates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.forced_certificates` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem forced_certificates : (∀ outside : Fin 12, ¬ (selected outside ∧ outside ≠ 1) → (¬ TwoAt Adj (fun vertex => selected vertex ∧ vertex ≠ 1) outside ↔ outside = 2)) ∧ (∀ outside : Fin 12, ¬ (selected outside ∧ outside ≠ 7) → (¬ TwoAt Adj (fun vertex => selected vertex ∧ vertex ≠ 7) outside ↔ outside = 10)).

**Theorem 1.11 (selected card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.selected_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.selected_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem selected_card : ((List.finRange 12).filter (fun vertex => decide (selected vertex))).length = 8.

**Definition 1.12 (membership).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.membership`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.membership` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def membership (mask : Fin 4096) (vertex : Fin 12) : Bool.

**Definition 1.13 (card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.card`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.card` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def card (mask : Fin 4096) : Nat.

**Definition 1.14 (Dissociation).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.Dissociation`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.Dissociation` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def Dissociation (mask : Fin 4096) : Prop.

**Theorem 1.15 (exchange collision).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.exchange_collision`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.exchange_collision` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem exchange_collision : (∀ vertex : Fin 12, membership 1909 vertex = true ↔ (selected vertex ∧ vertex ≠ 1 ∧ vertex ≠ 7) ∨ vertex = 2 ∨ vertex = 10) ∧ card 1909 = 8 ∧ ¬ Dissociation 1909.

**Theorem 1.16 (dissociation port cap).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.dissociation_port_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.dissociation_port_cap` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dissociation_port_cap : ∀ mask : Fin 4096, Dissociation mask → card mask ≤ 6 + if membership mask 0 || membership mask 6 then 1 else 0.

**Definition 1.17 (portWitness).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.portWitness`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.portWitness` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def portWitness (first second : Bool) : Fin 4096.

**Theorem 1.18 (port attainment).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.port_attainment`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.port_attainment` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem port_attainment (first second : Bool) : membership (portWitness first second) 0 = first ∧ membership (portWitness first second) 6 = second ∧ Dissociation (portWitness first second) ∧ card (portWitness first second) = 6 + (if first || second then 1 else 0) ∧ (∀ port ∈ ([0,6] : List (Fin 12)), membership (portWitness first second) port = true → ((neighbors port).filter (membership (portWitness first second))).length = 0).

**Definition 1.19 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph : SimpleGraph (Fin 12).

**Definition 1.20 (selectedSet).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.selectedSet`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.selectedSet` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def selectedSet : Finset (Fin 12).

**Definition 1.21 (maskSet).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.maskSet`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.maskSet` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def maskSet (mask : Fin 4096) : Finset (Fin 12).

**Theorem 1.22 (mask dissociation iff).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.mask_dissociation_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.mask_dissociation_iff` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem mask_dissociation_iff (mask : Fin 4096) : Dissociation mask ↔ IsKIndependent graph 2 (maskSet mask).

**Theorem 1.23 (beta graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.beta_graph`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.beta_graph` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_graph : beta graph 2 = 7.

**Theorem 1.24 (selectedSet minimal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.selectedSet_minimal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.selectedSet_minimal` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem selectedSet_minimal : IsMinimalStarForming graph 2 selectedSet.

**Theorem 1.25 (selectedSet card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.selectedSet_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.selectedSet_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem selectedSet_card : selectedSet.card = 8.

**Theorem 1.26 (graph gap).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.graph_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.graph_gap` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem graph_gap : beta graph 2 < SF graph 2.

**Theorem 1.27 (graph bipartite subcubic).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.graph_bipartite_subcubic`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.graph_bipartite_subcubic` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem graph_bipartite_subcubic : graph.Colorable 2 ∧ ∀ v, (Finset.univ.filter (graph.Adj v)).card ≤ 3.

**Definition 1.28 (claim).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.claim` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def claim : Prop.

**Theorem 1.29 (result).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.result` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem result : ¬ claim.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.Adj`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.Dissociation`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.adjacency_simple`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.base_deletion_failures`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.base_forms`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.base_minimal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.beta_graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.card`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.dissociation_port_cap`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.exchange_collision`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.failure`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.forced_certificates`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.graph_bipartite_subcubic`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.graph_gap`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.maskSet`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.mask_dissociation_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.membership`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.minimal_of_deletion_failures`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.neighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.portWitness`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.port_attainment`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.selected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.selectedSet`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.selectedSet_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.selectedSet_minimal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.selected_card`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/FiniteCover](FiniteCover.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/FiniteMasks](FiniteMasks.md)
