# Balanced isolates with positive compensation slack

## Abstract

Balanced isolates with positive compensation slack

For every d at least two, the actual disjoint union of two complete bipartite graphs Kdd is d-regular bipartite. The two components select opposite whole sides. The selected set is minimal forming and has two d vertices, all isolated, with exactly d on each color side. The actual dissociation maximum is two d, proved for every d by a side-count argument and finite attainment rather than bounded enumeration. Its regular budget is exactly the isolate count two d, but compensation slack is positive two d. This is the received disconnected counterexample to inferring linear equality from balanced isolate-tight accounting. It does not assert connectivity, the converse partition theorem or maximum-exchange classification.

**Definition 1.1 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph : SimpleGraph (Bool × Fin d).

**Definition 1.2 (part).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.part`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.part` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def part (b : Bool) : Finset (Bool × Fin d).

**Theorem 1.3 (mem part).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.mem_part`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.mem_part` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem mem_part (b : Bool) (v : Bool × Fin d) : v ∈ part d b ↔ v.1=b.

**Theorem 1.4 (part card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.part_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.part_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem part_card (b : Bool) : (part d b).card= d.

**Theorem 1.5 (neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.neighbors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.neighbors` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem neighbors (v : Bool × Fin d) : Finset.univ.filter ((graph d).Adj v) = part d (!v.1).

**Theorem 1.6 (regular).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.regular`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.regular` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem regular (v : Bool × Fin d) : degree (graph d) v= d.

**Theorem 1.7 (part independent).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.part_independent`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.part_independent` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem part_independent (b : Bool) : IsKIndependent (graph d) 2 (part d b).

**Theorem 1.8 (independent cap).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.independent_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.independent_cap` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem independent_cap (hd : 2 ≤ d) (S : Finset (Bool × Fin d)) (hS : IsKIndependent (graph d) 2 S) : S.card≤d.

**Theorem 1.9 (beta eq).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.beta_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.beta_eq` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_eq (hd : 2 ≤ d) : beta (graph d) 2= d.

**Theorem 1.10 (part minimal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.part_minimal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.part_minimal` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem part_minimal (hd : 2 ≤ d) (b : Bool) : IsMinimalStarForming (graph d) 2 (part d b).

**Definition 1.11 (pairGraph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.pairGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.pairGraph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev pairGraph.

**Definition 1.12 (selection).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.selection`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.selection` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def selection : Finset ((Bool × Fin d) ⊕ (Bool × Fin d)).

**Definition 1.13 (color).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.color`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.color` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def color : ((Bool × Fin d) ⊕ (Bool × Fin d)) → Bool | .inl v => v.1 | .inr v => v.1 theorem pair_coloring : (pairGraph d).Colorable 2.

**Theorem 1.14 (pair coloring).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.pair_coloring`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.pair_coloring` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pair_coloring : (pairGraph d).Colorable 2.

**Theorem 1.15 (pair regular).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.pair_regular`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.pair_regular` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pair_regular (v : (Bool × Fin d) ⊕ (Bool × Fin d)) : degree (pairGraph d) v= d.

**Theorem 1.16 (selection minimal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.selection_minimal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.selection_minimal` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem selection_minimal (hd : 2 ≤ d) : IsMinimalStarForming (pairGraph d) 2 (selection d).

**Theorem 1.17 (selection card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.selection_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.selection_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem selection_card : (selection d).card=2*d.

**Theorem 1.18 (pair beta).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.pair_beta`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.pair_beta` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pair_beta (hd : 2 ≤ d) : beta (pairGraph d) 2=2*d.

**Theorem 1.19 (selection isolates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.selection_isolates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.selection_isolates` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem selection_isolates : isolates (pairGraph d) (selection d)=selection d.

**Theorem 1.20 (color balance).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.color_balance`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.color_balance` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem color_balance : ((selection d).filter (fun v => color d v=false)).card= d ∧ ((selection d).filter (fun v => color d v=true)).card= d.

**Theorem 1.21 (tight but positive).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.tight_but_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.tight_but_positive` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem tight_but_positive (hd : 2 ≤ d) : (d:ℤ)*Fintype.card ((Bool × Fin d) ⊕ (Bool × Fin d)) - (2*(d:ℤ)-1)*(selection d).card = (isolates (pairGraph d) (selection d)).card ∧ (d:ℤ)*Fintype.card ((Bool × Fin d) ⊕ (Bool × Fin d)) + 2*(beta (pairGraph d) 2:ℤ) - (2*(d:ℤ)+1)*(selection d).card = 2*(d:ℤ) ∧ 0 < 2*(d:ℤ).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.beta_eq`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.color`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.color_balance`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.independent_cap`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.mem_part`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.neighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.pairGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.pair_beta`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.pair_coloring`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.pair_regular`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.part`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.part_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.part_independent`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.part_minimal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.regular`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.selection`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.selection_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.selection_isolates`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.selection_minimal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.tight_but_positive`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Comparison](Comparison.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity](DegreeCapacity.md)
