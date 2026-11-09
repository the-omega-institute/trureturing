# Actual sharp regular bipartite graphs

## Abstract

Actual sharp regular bipartite graphs

The graph has two bipartition sides, each consisting of a high class, an outside class and one hub. An arbitrary fixed-point-free permutation determines the two excluded outside incidences. Symbolic neighbor counts prove degree d, the actual high classes and hubs form a minimal selection of size 2d+2, and degree capacity proves SF exactly 2d+2 for d at least three. Actual crown and outside-neighbor counting proves beta exactly 2d+1 for d at least five. The cyclic d=3,4 boundaries, two-connectivity, all-degree square weights and broken-edge rings are separate obligations.

**Definition 1.1 (Side).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.Side`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.Side` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev Side (I : Type).

**Definition 1.2 (Vertex).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.Vertex`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.Vertex` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev Vertex (I : Type).

**Definition 1.3 (link).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.link`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.link` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def link (next : Equiv.Perm I) : Side I → Side I → Prop | none,none => False | none,some (k,_) => k = true | some (k,_),none => k = true | some (false,i),some (false,j) => i ≠ j | some (false,i),some (true,j) => i = j | some (true,i),some (false,j) => i = j | some (true,i),some (true,j) => j ≠ next i ∧ j ≠ next (next i) instance (next : Equiv.Perm I) : DecidableRel (link next).

**Definition 1.4 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph (next : Equiv.Perm I) : SimpleGraph (Vertex I).

**Theorem 1.5 (bipartite).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.bipartite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.bipartite` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem bipartite (next : Equiv.Perm I) : (graph next).Colorable 2.

**Theorem 1.6 (regular).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.regular`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.regular` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem regular (next : Equiv.Perm I) (hnext : ∀ i, next i ≠ i) (v : Vertex I) : DegreeCapacity.degree (graph next) v = Fintype.card I.

**Definition 1.7 (selected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.selected`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.selected` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def selected : Side I → Prop | none => True | some (k,_) => k = false instance : DecidablePred (@selected I).

**Definition 1.8 (selection).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.selection`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.selection` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def selection : Finset (Vertex I).

**Theorem 1.9 (selection minimal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.selection_minimal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.selection_minimal` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem selection_minimal (next : Equiv.Perm I) : IsMinimalStarForming (graph next) 2 selection.

**Theorem 1.10 (selection card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.selection_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.selection_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem selection_card : (selection : Finset (Vertex I)).card = 2 * Fintype.card I + 2.

**Theorem 1.11 (sf graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.sf_graph`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.sf_graph` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem sf_graph (next : Equiv.Perm I) (hnext : ∀ i, next i ≠ i) (hd : 3 ≤ Fintype.card I) : SF (graph next) 2 = 2 * Fintype.card I + 2.

**Theorem 1.12 (dissociation cap ge five).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.dissociation_cap_ge_five`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.dissociation_cap_ge_five` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dissociation_cap_ge_five (next : Equiv.Perm I) (hd : 5 ≤ Fintype.card I) (D : Finset (Vertex I)) (hD : IsKIndependent (graph next) 2 D) : D.card ≤ 2 * Fintype.card I + 1.

**Theorem 1.13 (beta graph ge five).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.beta_graph_ge_five`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.beta_graph_ge_five` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_graph_ge_five (next : Equiv.Perm I) (hd : 5 ≤ Fintype.card I) : beta (graph next) 2 = 2 * Fintype.card I + 1.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.Side`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.beta_graph_ge_five`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.bipartite`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.dissociation_cap_ge_five`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.link`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.regular`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.selected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.selection`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.selection_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.selection_minimal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SharpRegular.sf_graph`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/PrivateClauses](PrivateClauses.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/RegularCompensation](RegularCompensation.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate](SubcubicCertificate.md)
