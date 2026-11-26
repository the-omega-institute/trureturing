# Actual variable-size four-port assemblies

## Abstract

Actual variable-size four-port assemblies

Every module has its own finite core type, permutation and marked cell. An independent module permutation joins exactly the remaining two degree-two ports. This includes all positive unequal core sizes and singleton seam restoration. Each disjoint actual module pays its own strict loss; the dependent fiber sum proves exact beta and the original forming set attains SF after outside-only rewiring. Structural connectivity requires a separate argument.

**Definition 1.1 (Vertex).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.Vertex`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.Vertex` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev Vertex.

**Definition 1.2 (Within).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.Within`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.Within` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: inductive Within (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) : Vertex K → Vertex K → Prop | intro (j : J) (v w : PaddingModule.Vertex (K j)) (h : (PaddingModule.graph (q j) (mark j)).Adj v w) : Within q mark ⟨j,v⟩ ⟨j,w⟩ variable {K} private theorem within_same (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (j : J) (v w : PaddingModule.Vertex (K j)) : Within K q mark ⟨j,v⟩ ⟨j,w⟩ ↔ (PaddingModule.graph (q j) (mark j)).Adj v w.

**Definition 1.3 (left).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.left`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.left` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def left (mark : ∀ j, K j) (j : J) : Vertex K.

**Definition 1.4 (right).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.right`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.right` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def right (mark : ∀ j, K j) (j : J) : Vertex K.

**Definition 1.5 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) : SimpleGraph (Vertex K).

**Definition 1.6 (neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.neighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.neighbors` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def neighbors (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) (x : Vertex K) : Finset (Vertex K).

**Theorem 1.7 (mem neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.mem_neighbors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.mem_neighbors` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem mem_neighbors (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) (x y : Vertex K) : y ∈ neighbors q mark e x ↔ (graph q mark e).Adj x y.

**Definition 1.8 (slice).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.slice`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.slice` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def slice (S : Finset (Vertex K)) (j : J) : Finset (PaddingModule.Vertex (K j)).

**Theorem 1.9 (card slices).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.card_slices`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.card_slices` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem card_slices (S : Finset (Vertex K)) : S.card=∑ j, (slice S j).card.

**Theorem 1.10 (beta upper).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.beta_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.beta_upper` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_upper (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) : beta (graph q mark e) 2 ≤ 7*Fintype.card J+12*∑ j, Fintype.card (K j).

**Theorem 1.11 (regular).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.regular`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.regular` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem regular (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) (x : Vertex K) : DegreeCapacity.degree (graph q mark e) x=3.

**Theorem 1.12 (bipartite).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.bipartite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.bipartite` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem bipartite (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) : (graph q mark e).Colorable 2.

**Definition 1.13 (independent).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.independent`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.independent` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def independent : Finset (Vertex K).

**Definition 1.14 (forming).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.forming`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.forming` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def forming : Finset (Vertex K).

**Theorem 1.15 (independent valid).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.independent_valid`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.independent_valid` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem independent_valid (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) : IsKIndependent (graph q mark e) 2 independent.

**Theorem 1.16 (independent card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.independent_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.independent_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem independent_card : (independent : Finset (Vertex K)).card= 7*Fintype.card J+12*∑ j, Fintype.card (K j).

**Theorem 1.17 (forming card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.forming_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.forming_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem forming_card : (forming : Finset (Vertex K)).card= 8*Fintype.card J+12*∑ j, Fintype.card (K j).

**Theorem 1.18 (order).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.order`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.order` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem order : Fintype.card (Vertex K)=14*Fintype.card J+20*∑ j, Fintype.card (K j).

**Theorem 1.19 (forming minimal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.forming_minimal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.forming_minimal` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem forming_minimal (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) : IsMinimalStarForming (graph q mark e) 2 forming.

**Theorem 1.20 (parameters).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem parameters (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) : beta (graph q mark e) 2 = 7*Fintype.card J+12*∑ j, Fintype.card (K j) ∧ SF (graph q mark e) 2 = 8*Fintype.card J+12*∑ j, Fintype.card (K j).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.Within`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.beta_upper`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.bipartite`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.card_slices`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.forming`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.forming_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.forming_minimal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.independent`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.independent_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.independent_valid`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.left`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.mem_neighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.neighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.order`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.parameters`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.regular`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.right`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingRings.slice`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/PaddingModule](PaddingModule.md)
