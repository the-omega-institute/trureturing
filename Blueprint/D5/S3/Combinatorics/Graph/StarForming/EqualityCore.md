# Actual periodic cubic equality cores

## Abstract

Actual periodic cubic equality cores

The actual twenty-vertex cell graph is defined for every finite index type and every index permutation, including fixed points and the empty family. Symbolic neighbor rows prove cubic regularity and a common bipartition. The H/U minimal selection and the explicit matching dissociation selection both have twelve vertices per cell. Global degree capacity and actual attainment prove beta and SF each equal twelve times the cell count. Cyclic connectivity, padding attachments and four-port ring losses are separate obligations.

**Definition 1.1 (edges).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.edges`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.edges` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def edges : Finset (Fin 20 × Fin 20).

**Definition 1.2 (internal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.internal`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.internal` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev internal (v w : Fin 20) : Prop.

**Definition 1.3 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph (next : Equiv.Perm I) : SimpleGraph (I × Fin 20).

**Definition 1.4 (neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.neighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.neighbors` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def neighbors (next : Equiv.Perm I) (x : I × Fin 20) : Finset (I × Fin 20).

**Theorem 1.5 (mem neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.mem_neighbors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.mem_neighbors` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem mem_neighbors (next : Equiv.Perm I) (x y : I × Fin 20) : y ∈ neighbors next x ↔ (graph next).Adj x y.

**Theorem 1.6 (regular).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.regular`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.regular` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem regular (next : Equiv.Perm I) (x : I × Fin 20) : DegreeCapacity.degree (graph next) x = 3.

**Definition 1.7 (color).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.color`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.color` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def color (v : Fin 20) : Bool.

**Theorem 1.8 (bipartite).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.bipartite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.bipartite` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem bipartite (next : Equiv.Perm I) : (graph next).Colorable 2.

**Definition 1.9 (selected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.selected`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.selected` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev selected (v : Fin 20) : Prop.

**Definition 1.10 (dissociation).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.dissociation`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.dissociation` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev dissociation (v : Fin 20) : Prop.

**Definition 1.11 (S).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.S`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.S` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def S : Finset (I × Fin 20).

**Definition 1.12 (D).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.D`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.D` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def D : Finset (I × Fin 20).

**Theorem 1.13 (D valid).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.D_valid`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.D_valid` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem D_valid (next : Equiv.Perm I) : IsKIndependent (graph next) 2 D.

**Theorem 1.14 (S minimal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.S_minimal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.S_minimal` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem S_minimal (next : Equiv.Perm I) : IsMinimalStarForming (graph next) 2 S.

**Theorem 1.15 (selected card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.selected_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.selected_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem selected_card : (S : Finset (I × Fin 20)).card = 12 * Fintype.card I.

**Theorem 1.16 (dissociation card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.dissociation_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.dissociation_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dissociation_card : (D : Finset (I × Fin 20)).card = 12 * Fintype.card I.

**Theorem 1.17 (exact parameters).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.exact_parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.exact_parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem exact_parameters (next : Equiv.Perm I) : beta (graph next) 2 = 12 * Fintype.card I ∧ SF (graph next) 2 = 12 * Fintype.card I.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.D`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.D_valid`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.S`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.S_minimal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.bipartite`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.color`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.dissociation`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.dissociation_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.edges`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.exact_parameters`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.internal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.mem_neighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.neighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.regular`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.selected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.selected_card`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/PrivateClauses](PrivateClauses.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/RegularCompensation](RegularCompensation.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate](SubcubicCertificate.md)
