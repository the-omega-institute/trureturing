# Pappus half-order refutation

## Abstract

Pappus half-order refutation

The certified Pappus graph is cubic, bipartite and C4-free, with dissociation maximum ten. It refutes the half-order bound at order eighteen. The parity labeling also supplies the common input to the representative proofs.

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

**Definition 1.8 (Pappus parity coloring).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusColor`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusColor` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def pappusColor (v : Fin 18) : Bool.

**Theorem 1.9 (Pappus parity coloring is proper).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusColor_valid`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusColor_valid` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Adjacent Pappus vertices have different parity labels by the certified adjacency table.

**Theorem 1.10 (Equal parity classes).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.paritySide_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.paritySide_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every even initial interval Fin (2 * n), each parity class has n elements by the general residue count.

**Theorem 1.11 (pappus class).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_class`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_class` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pappus_class : pappusGraph.Colorable 2 ∧ (∀ v, DegreeCapacity.degree pappusGraph v = 3) ∧ NoFourCycle pappusGraph.Adj.

**Theorem 1.12 (pappus selection).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_selection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_selection` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pappus_selection : IsKIndependent pappusGraph 2 pappusSet ∧ pappusSet.card = 10.

**Theorem 1.13 (beta pappus).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.beta_pappus`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.beta_pappus` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_pappus : beta pappusGraph 2 = 10.

**Definition 1.14 (claim).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.claim` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def claim : Prop.

**Theorem 1.15 (result).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.result` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

There is no universal half-order bound 2 * beta G 2 ≤ 18 for all cubic bipartite C4-free graphs G on Fin 18. The certified Pappus graph gives beta G 2 = 10.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.beta_pappus`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusColor`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusColor_valid`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusNeighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusSelected`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusSet`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_class`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_dissociation_certificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_no_four_cycle_certificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_regular_bipartite_certificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_selection`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.paritySide_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.result`
- Dependency: [D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds](C4RepresentativeBounds.md)
