# Exact canonical Heawood invariants

## Abstract

Exact canonical Heawood invariants

The original Fano graph and supplier minimal eight-set are reused. The exact finite dissociation cap ranges over every subset of this fixed fourteen-vertex graph, and an actual bipartition side attains seven. The general degree-capacity theorem bounds every minimal selection by eight. Thus beta two is seven and SF two is eight for this cubic bipartite graph, refuting the universal cubic bipartite identification. This does not prove the all-r interface, cover or graph-structure assertions.

**Definition 1.1 (fanoNeighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fanoNeighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fanoNeighbors` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def fanoNeighbors (vertex : Fin 14) : List (Fin 14).

**Definition 1.2 (FanoAdj).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.FanoAdj`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.FanoAdj` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def FanoAdj (first second : Fin 14) : Prop.

**Definition 1.3 (fanoSelected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fanoSelected`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fanoSelected` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def fanoSelected (vertex : Fin 14) : Prop.

**Definition 1.4 (fanoFailure).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fanoFailure`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fanoFailure` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def fanoFailure (vertex : Fin 14) : Fin 14.

**Theorem 1.5 (fano simple cubic).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fano_simple_cubic`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fano_simple_cubic` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem fano_simple_cubic : (∀ vertex : Fin 14, ¬ FanoAdj vertex vertex) ∧ (∀ first second : Fin 14, FanoAdj first second ↔ FanoAdj second first) ∧ (∀ vertex : Fin 14, (fanoNeighbors vertex).length = 3 ∧ (fanoNeighbors vertex).Nodup).

**Theorem 1.6 (fano forms).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fano_forms`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fano_forms` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem fano_forms : Forms FanoAdj fanoSelected.

**Theorem 1.7 (fano deletion failures).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fano_deletion_failures`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fano_deletion_failures` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem fano_deletion_failures : ∀ deleted : Fin 14, fanoSelected deleted → ¬ (fanoSelected (fanoFailure deleted) ∧ fanoFailure deleted ≠ deleted) ∧ ¬ TwoAt FanoAdj (fun vertex => fanoSelected vertex ∧ vertex ≠ deleted) (fanoFailure deleted).

**Theorem 1.8 (fano minimal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fano_minimal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fano_minimal` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem fano_minimal : Minimal FanoAdj fanoSelected.

**Theorem 1.9 (fano selected card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fano_selected_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fano_selected_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem fano_selected_card : ((List.finRange 14).filter (fun vertex => decide (fanoSelected vertex))).length = 8.

**Definition 1.10 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph : SimpleGraph (Fin 14).

**Definition 1.11 (selectedSet).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.selectedSet`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.selectedSet` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def selectedSet : Finset (Fin 14).

**Definition 1.12 (maskSet).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.maskSet`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.maskSet` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def maskSet (mask : Fin 16384) : Finset (Fin 14).

**Definition 1.13 (maskDissociates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.maskDissociates`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.maskDissociates` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def maskDissociates (mask : Fin 16384) : Prop.

**Theorem 1.14 (mask dissociation iff).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.mask_dissociation_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.mask_dissociation_iff` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem mask_dissociation_iff (mask : Fin 16384) : maskDissociates mask ↔ IsKIndependent graph 2 (maskSet mask).

**Theorem 1.15 (mask cap).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.mask_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.mask_cap` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem mask_cap (mask : Fin 16384) (h : maskDissociates mask) : ((List.finRange 14).filter (fun v => mask.val.testBit v.val)).length ≤ 7.

**Theorem 1.16 (beta graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.beta_graph`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.beta_graph` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_graph : beta graph 2 = 7.

**Theorem 1.17 (sf graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.sf_graph`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.sf_graph` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem sf_graph : SF graph 2 = 8.

**Theorem 1.18 (graph class).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.graph_class`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.graph_class` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem graph_class : graph.Colorable 2 ∧ ∀ v, (Finset.univ.filter (graph.Adj v)).card = 3.

**Definition 1.19 (claim).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.claim` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def claim : Prop.

**Theorem 1.20 (result).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.result` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem result : ¬ claim.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.FanoAdj`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.beta_graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fanoFailure`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fanoNeighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fanoSelected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fano_deletion_failures`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fano_forms`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fano_minimal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fano_selected_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.fano_simple_cubic`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.graph_class`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.maskDissociates`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.maskSet`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.mask_cap`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.mask_dissociation_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.selectedSet`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.sf_graph`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CubicCertificate](CubicCertificate.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity](DegreeCapacity.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/FiniteMasks](FiniteMasks.md)
