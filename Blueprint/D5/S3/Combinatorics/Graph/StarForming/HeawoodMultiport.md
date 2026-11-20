# The actual second-cut local obstruction

## Abstract

The actual second-cut local obstruction

The original thirty-four-vertex adjacency rows, twenty-set, color data, cut edges and finite certificates are retained. The actual graph is bipartite of maximum degree three and the actual twenty-set is dissociation, refuting its proposed cap nineteen. This is a local second-cut obstruction and does not refute global compensation or assert beta exactly twenty.

**Definition 1.1 (rows).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.rows`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.rows` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def rows : List (List Nat).

**Definition 1.2 (adjacency).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.adjacency`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.adjacency` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def adjacency (first second : Fin 34) : Prop.

**Definition 1.3 (chosen).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.chosen`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.chosen` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def chosen : List Nat.

**Definition 1.4 (selected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.selected`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.selected` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def selected (vertex : Fin 34) : Prop.

**Definition 1.5 (selectedDegree).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.selectedDegree`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.selectedDegree` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def selectedDegree (vertex : Fin 34) : Nat.

**Definition 1.6 (unjoined).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.unjoined`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.unjoined` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def unjoined (first second : Fin 34) : Prop.

**Definition 1.7 (color).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.color`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.color` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def color (vertex : Fin 34) : Nat.

**Theorem 1.8 (witness dissociates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.witness_dissociates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.witness_dissociates` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem witness_dissociates : Dissociates adjacency selected.

**Theorem 1.9 (witness cardinality).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.witness_cardinality`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.witness_cardinality` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem witness_cardinality : ((List.finRange 34).filter (fun vertex => decide (selected vertex))).length = 20.

**Theorem 1.10 (simple subcubic).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.simple_subcubic`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.simple_subcubic` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem simple_subcubic : (∀ vertex, ¬ adjacency vertex vertex) ∧ (∀ first second, adjacency first second ↔ adjacency second first) ∧ (∀ vertex, ((List.finRange 34).filter (fun neighbor => decide (adjacency vertex neighbor))).length ≤ 3).

**Theorem 1.11 (bipartite).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.bipartite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.bipartite` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem bipartite : ∀ first second, adjacency first second → color first ≠ color second.

**Theorem 1.12 (attachment isolates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.attachment_isolates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.attachment_isolates` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem attachment_isolates : ∀ vertex : Fin 34, [12, 13, 20, 28].contains vertex.val = true → selected vertex ∧ ∀ neighbor, unjoined vertex neighbor → ¬ selected neighbor.

**Theorem 1.13 (external port profile).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.external_port_profile`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.external_port_profile` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem external_port_profile : (∀ vertex : Fin 34, [15, 16, 24, 32].contains vertex.val = true → selected vertex ∧ selectedDegree vertex = 1) ∧ (∀ vertex : Fin 34, [14, 17].contains vertex.val = true → ¬ selected vertex) ∧ (∀ vertex : Fin 34, ((List.finRange 34).filter (fun neighbor => decide (adjacency vertex neighbor))).length = 2 ↔ [14, 15, 16, 17, 24, 32].contains vertex.val = true).

**Definition 1.14 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph : SimpleGraph (Fin 34).

**Definition 1.15 (selectedSet).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.selectedSet`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.selectedSet` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def selectedSet : Finset (Fin 34).

**Theorem 1.16 (graph class).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.graph_class`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.graph_class` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem graph_class : graph.Colorable 2 ∧ ∀ v, DegreeCapacity.degree graph v ≤ 3.

**Theorem 1.17 (selection).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.selection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.selection` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem selection : IsKIndependent graph 2 selectedSet ∧ selectedSet.card = 20.

**Definition 1.18 (claim).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.claim` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def claim : Prop.

**Theorem 1.19 (result).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.result` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem result : ¬ claim.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.adjacency`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.attachment_isolates`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.bipartite`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.chosen`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.color`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.external_port_profile`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.graph_class`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.rows`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.selected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.selectedDegree`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.selectedSet`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.selection`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.simple_subcubic`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.unjoined`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.witness_cardinality`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.witness_dissociates`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity](DegreeCapacity.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DissociationCover](DissociationCover.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/FiniteMasks](FiniteMasks.md)
