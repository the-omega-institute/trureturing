# Exact canonical Heawood invariants

## Abstract

Exact canonical Heawood invariants

The original Fano graph and supplier minimal eight-set are reused. The exact finite dissociation cap ranges over every subset of this fixed fourteen-vertex graph, and an actual bipartition side attains seven. The general degree-capacity theorem bounds every minimal selection by eight. Thus beta two is seven and SF two is eight for this cubic bipartite graph, refuting the universal cubic bipartite identification. This does not prove the all-r interface, cover or graph-structure assertions.

**Definition 1.1 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph : SimpleGraph (Fin 14).

**Definition 1.2 (selectedSet).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.selectedSet`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.selectedSet` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def selectedSet : Finset (Fin 14).

**Definition 1.3 (maskSet).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.maskSet`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.maskSet` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def maskSet (mask : Fin 16384) : Finset (Fin 14).

**Definition 1.4 (maskDissociates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.maskDissociates`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.maskDissociates` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def maskDissociates (mask : Fin 16384) : Prop.

**Theorem 1.5 (mask dissociation iff).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.mask_dissociation_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.mask_dissociation_iff` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem mask_dissociation_iff (mask : Fin 16384) : maskDissociates mask ↔ IsKIndependent graph 2 (maskSet mask).

**Theorem 1.6 (mask cap).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.mask_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.mask_cap` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem mask_cap (mask : Fin 16384) (h : maskDissociates mask) : ((List.finRange 14).filter (fun v => mask.val.testBit v.val)).length ≤ 7.

**Theorem 1.7 (beta graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.beta_graph`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.beta_graph` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_graph : beta graph 2 = 7.

**Theorem 1.8 (sf graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.sf_graph`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.sf_graph` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem sf_graph : SF graph 2 = 8.

**Theorem 1.9 (graph class).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.graph_class`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.graph_class` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem graph_class : graph.Colorable 2 ∧ ∀ v, (Finset.univ.filter (graph.Adj v)).card = 3.

**Definition 1.10 (claim).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.claim` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def claim : Prop.

**Theorem 1.11 (result).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.result` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem result : ¬ claim.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.beta_graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.claim`
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
