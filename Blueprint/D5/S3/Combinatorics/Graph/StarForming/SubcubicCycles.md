# Actual even cyclic shared-port parameters

## Abstract

Actual even cyclic shared-port parameters

Alternating cells give the actual bipartition and a displayed perfect matching. The graph has eleven vertices and fourteen edges per cell, five degree-two and six degree-three vertices. For positive even r the actual finite maxima SF, beta, alpha and Gamma have their stated exact values, including r two. This does not assert planarity or the separate cycle-graph theorem.

**Definition 1.1 (color).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.color`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.color` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def color (phase : I → Bool) (x : I × Fin 11) : Fin 2.

**Theorem 1.2 (bipartite).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.bipartite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.bipartite` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem bipartite (next : Equiv.Perm I) (phase : I → Bool) (hp : ∀ i, phase (next i)= !(phase i)) : (graph next).Colorable 2.

**Definition 1.3 (mate).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.mate`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.mate` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def mate (next : Equiv.Perm I) (phase : I → Bool) (x : I × Fin 11) : I × Fin 11.

**Theorem 1.4 (alpha half).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.alpha_half`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.alpha_half` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem alpha_half (next : Equiv.Perm I) (phase : I → Bool) (hp : ∀ i, phase (next i)= !(phase i)) : 2*(graph next).indepNum=11*Fintype.card I.

**Theorem 1.5 (degree counts).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.degree_counts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.degree_counts` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem degree_counts (next : Equiv.Perm I) : (Finset.univ.filter (fun x => DegreeCapacity.degree (graph next) x=2)).card=5*Fintype.card I ∧ (Finset.univ.filter (fun x => DegreeCapacity.degree (graph next) x=3)).card=6*Fintype.card I.

**Theorem 1.6 (edge count).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.edge_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.edge_count` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem edge_count (next : Equiv.Perm I) : (graph next).edgeFinset.card=14*Fintype.card I.

**Definition 1.7 (cyclicPhase).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.cyclicPhase`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.cyclicPhase` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def cyclicPhase {r : ℕ} (i : Fin r) : Bool.

**Theorem 1.8 (cyclic phase).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.cyclic_phase`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.cyclic_phase` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem cyclic_phase (r : ℕ) (hr : 0<r) (he : Even r) : ∀ i : Fin r, cyclicPhase (finRotate r i)= !(cyclicPhase i).

**Theorem 1.9 (cyclic parameters).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.cyclic_parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.cyclic_parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem cyclic_parameters (r : ℕ) (hr : 0<r) (he : Even r) : let G.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.alpha_half`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.bipartite`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.color`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.cyclicPhase`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.cyclic_parameters`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.cyclic_phase`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.degree_counts`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.edge_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.mate`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DominationComparison](DominationComparison.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta](SubcubicIdentificationBeta.md)
