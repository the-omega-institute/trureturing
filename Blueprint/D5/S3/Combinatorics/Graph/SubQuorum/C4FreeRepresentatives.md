# Finite C4-free representative instances

## Abstract

Finite C4-free representative instances

The exact Pappus cubic bipartite C4-free graph has beta, psiSq and Omega ten, empty optimal matching and distinct-color dissociation support at ten colors. The actual Heawood parameter distinction and binary-label mixed-support optimum retain their finite scope. The typed Pappus claim/result refutes extending the half-order bound to order eighteen. Positive finite consequences are not certified exempt from utility review.

**Definition 1.1 (pappusNeighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusNeighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusNeighbors` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def pappusNeighbors (vertex : Fin 18) : List Nat.

**Definition 1.2 (pappusSelected).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusSelected`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusSelected` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def pappusSelected : List Nat.

**Theorem 1.3 (pappus regular bipartite certificate).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_regular_bipartite_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_regular_bipartite_certificate` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pappus_regular_bipartite_certificate : (∀ vertex : Fin 18, (pappusNeighbors vertex).length = 3 ∧ (pappusNeighbors vertex).Nodup ∧ ∀ neighbor, neighbor ∈ pappusNeighbors vertex → neighbor < 18 ∧ neighbor % 2 ≠ vertex.val % 2) ∧ (∀ first second : Fin 18, second.val ∈ pappusNeighbors first ↔ first.val ∈ pappusNeighbors second).

**Theorem 1.4 (pappus no four cycle certificate).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_no_four_cycle_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_no_four_cycle_certificate` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pappus_no_four_cycle_certificate : ∀ first second : Fin 18, first ≠ second → ((pappusNeighbors first).filter (fun vertex => (pappusNeighbors second).contains vertex)).length ≤ 1.

**Theorem 1.5 (pappus dissociation certificate).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_dissociation_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_dissociation_certificate` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pappus_dissociation_certificate : pappusSelected.length = 10 ∧ pappusSelected.Nodup ∧ (∀ vertex, vertex ∈ pappusSelected → vertex < 18) ∧ (∀ vertex : Fin 18, vertex.val ∈ pappusSelected → ((pappusNeighbors vertex).filter (fun neighbor => pappusSelected.contains neighbor)).length ≤ 1).

**Definition 1.6 (pappusGraph).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusGraph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def pappusGraph : SimpleGraph (Fin 18).

**Definition 1.7 (pappusSet).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusSet`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusSet` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def pappusSet : Finset (Fin 18).

**Theorem 1.8 (pappus class).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_class`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_class` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pappus_class : pappusGraph.Colorable 2 ∧ (∀ v, DegreeCapacity.degree pappusGraph v = 3) ∧ NoFourCycle pappusGraph.Adj.

**Theorem 1.9 (pappus selection).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_selection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_selection` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pappus_selection : IsKIndependent pappusGraph 2 pappusSet ∧ pappusSet.card = 10.

**Theorem 1.10 (beta pappus).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.beta_pappus`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.beta_pappus` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_pappus : beta pappusGraph 2 = 10.

**Definition 1.11 (claim).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.claim` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def claim : Prop.

**Theorem 1.12 (result).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.result` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem result : ¬ claim.

**Theorem 1.13 (heawood parameters).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.heawood_parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.heawood_parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem heawood_parameters : beta HeawoodParameters.graph 2 = 7 ∧ psiSq HeawoodParameters.graph = 7 ∧ Omega HeawoodParameters.graph = 7 ∧ SF HeawoodParameters.graph 2 = 8.

**Definition 1.14 (binaryHeawood).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.binaryHeawood`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.binaryHeawood` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def binaryHeawood : SimpleGraph (Fin 14).

**Definition 1.15 (mixedSingletons).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.mixedSingletons`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.mixedSingletons` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def mixedSingletons : Finset (Fin 14).

**Definition 1.16 (mixedMatching).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.mixedMatching`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.mixedMatching` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def mixedMatching : Finset (Fin 14 × Fin 14).

**Theorem 1.17 (mixed support optimum).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.mixed_support_optimum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.mixed_support_optimum` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem mixed_support_optimum : Feasible binaryHeawood mixedSingletons mixedMatching ∧ mixedSingletons.card + mixedMatching.card = Omega binaryHeawood ∧ (mixedSingletons.filter (fun v => heawoodColor v = false)).card = 3 ∧ (mixedSingletons.filter (fun v => heawoodColor v = true)).card = 3.

**Theorem 1.18 (omega pappus).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.omega_pappus`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.omega_pappus` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem omega_pappus : Omega pappusGraph = 10.

**Theorem 1.19 (pappus parameters).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pappus_parameters : beta pappusGraph 2 = 10 ∧ psiSq pappusGraph = 10 ∧ Omega pappusGraph = 10.

**Theorem 1.20 (pappus optimal matching empty).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_optimal_matching_empty`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_optimal_matching_empty` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pappus_optimal_matching_empty (T : Finset (Fin 18)) (M : Finset (Fin 18 × Fin 18)) (hf : Feasible pappusGraph T M) (hc : T.card + M.card = 10) : M = ∅.

**Theorem 1.21 (pappus coloring rigidity).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_coloring_rigidity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_coloring_rigidity` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pappus_coloring_rigidity (c : Fin 18 → Option ℕ) (hc : IsSubQuorum pappusGraph c) (hp : (palette c Finset.univ).card = 10) : IsKIndependent pappusGraph 2 (coloredSupport c Finset.univ) ∧ (coloredSupport c Finset.univ).card = 10 ∧ Set.InjOn c (coloredSupport c Finset.univ).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.beta_pappus`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.binaryHeawood`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.heawood_parameters`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.mixedMatching`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.mixedSingletons`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.mixed_support_optimum`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.omega_pappus`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusNeighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusSelected`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusSet`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_class`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_coloring_rigidity`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_dissociation_certificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_no_four_cycle_certificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_optimal_matching_empty`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_parameters`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_regular_bipartite_certificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_selection`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.result`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates](../StarForming/HeawoodCertificates.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters](../StarForming/HeawoodParameters.md)
- Dependency: [D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds](C4RepresentativeBounds.md)
