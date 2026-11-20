# Actual Heawood interfaces and loop-aware dissociation optimization

## Abstract

Actual Heawood interfaces and loop-aware dissociation optimization

The original fourteen-vertex blocks are joined by any simple graph on their two ports. Restored incidences, same-part edges, disconnected and empty finite families are allowed. The original port-omitting minimal eight-set and actual ambient slice cap prove SF=8|I|. The saturated-port theorem forces every dissociation eight-block to be a loop-free independent interaction vertex. Conversely the original eight/seven selections on an attaining loop-aware independent set give actual dissociation attainment, proving beta=7|I|+alpha0. Branching interfaces are counted directly with no cyclic charge reuse. Cyclic and reciprocal connectivity, Gamma/alpha and structural graph properties remain separate obligations.

**Definition 1.1 (port).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.port`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.port` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def port (p : Fin 2) : Fin 14.

**Definition 1.2 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph {I : Type} (P : SimpleGraph (I × Fin 2)) : SimpleGraph (I × Fin 14).

**Theorem 1.3 (chosen minimal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.chosen_minimal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.chosen_minimal` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem chosen_minimal (P : SimpleGraph (I × Fin 2)) : IsMinimalStarForming (graph P) 2 chosen.

**Theorem 1.4 (slice cap).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.slice_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.slice_cap` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem slice_cap (P : SimpleGraph (I × Fin 2)) (S : Finset (I × Fin 14)) (hS : IsMinimalStarForming (graph P) 2 S) (i : I) : (slice S i).card ≤ 8.

**Theorem 1.5 (sf graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.sf_graph`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.sf_graph` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem sf_graph (P : SimpleGraph (I × Fin 2)) : SF (graph P) 2 = 8 * Fintype.card I.

**Definition 1.6 (interaction).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.interaction`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.interaction` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def interaction (P : SimpleGraph (I × Fin 2)) (i j : I) : Prop.

**Definition 1.7 (IndependentBlocks).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.IndependentBlocks`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.IndependentBlocks` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def IndependentBlocks (P : SimpleGraph (I × Fin 2)) (A : Finset I) : Prop.

**Theorem 1.8 (beta graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.beta_graph`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.beta_graph` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_graph (P : SimpleGraph (I × Fin 2)) : beta (graph P) 2 = 7 * Fintype.card I + alpha0 P.

**Definition 1.9 (VertexCoverBlocks).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.VertexCoverBlocks`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.VertexCoverBlocks` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def VertexCoverBlocks (P : SimpleGraph (I × Fin 2)) (C : Finset I) : Prop.

**Theorem 1.10 (alpha0 add tau0).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.alpha0_add_tau0`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.alpha0_add_tau0` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem alpha0_add_tau0 (P : SimpleGraph (I × Fin 2)) : alpha0 P + tau0 P = Fintype.card I.

**Theorem 1.11 (gap eq tau0).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.gap_eq_tau0`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.gap_eq_tau0` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem gap_eq_tau0 (P : SimpleGraph (I × Fin 2)) : SF (graph P) 2 - beta (graph P) 2 = tau0 P.

**Theorem 1.12 (sf eq beta iff).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.sf_eq_beta_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.sf_eq_beta_iff` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem sf_eq_beta_iff (P : SimpleGraph (I × Fin 2)) : SF (graph P) 2 = beta (graph P) 2 ↔ P = ⊥.

**Theorem 1.13 (bipartite).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.bipartite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.bipartite` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem bipartite (P : SimpleGraph (I × Fin 2)) (hP : ∀ i j p q, P.Adj (i,p) (j,q) → p ≠ q) : (graph P).Colorable 2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.IndependentBlocks`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.VertexCoverBlocks`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.alpha0_add_tau0`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.beta_graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.bipartite`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.chosen_minimal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.gap_eq_tau0`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.interaction`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.port`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.sf_eq_beta_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.sf_graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.slice_cap`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CubicExact](CubicExact.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DominationComparison](DominationComparison.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters](HeawoodParameters.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodPorts](HeawoodPorts.md)
