# Heawood representative instances

## Abstract

Heawood representative instances

The cyclic-label Heawood graph has beta, psiSq and Omega seven and SF eight. The binary-label graph has an optimum with three singletons on each side and one matching edge. These finite positive certificates have no qualifying refutation basis under CLAUDE.md §3.3.

**Theorem 1.1 (heawood parameters).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/HeawoodRepresentatives.heawood_parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/HeawoodRepresentatives.heawood_parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem heawood_parameters : beta HeawoodParameters.graph 2 = 7 ∧ psiSq HeawoodParameters.graph = 7 ∧ Omega HeawoodParameters.graph = 7 ∧ SF HeawoodParameters.graph 2 = 8.

**Definition 1.2 (binaryHeawood).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/HeawoodRepresentatives.binaryHeawood`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/HeawoodRepresentatives.binaryHeawood` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def binaryHeawood : SimpleGraph (Fin 14).

**Definition 1.3 (mixedSingletons).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/HeawoodRepresentatives.mixedSingletons`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/HeawoodRepresentatives.mixedSingletons` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def mixedSingletons : Finset (Fin 14).

**Definition 1.4 (mixedMatching).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/HeawoodRepresentatives.mixedMatching`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/HeawoodRepresentatives.mixedMatching` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def mixedMatching : Finset (Fin 14 × Fin 14).

**Theorem 1.5 (mixed support optimum).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/HeawoodRepresentatives.mixed_support_optimum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/HeawoodRepresentatives.mixed_support_optimum` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem mixed_support_optimum : Feasible binaryHeawood mixedSingletons mixedMatching ∧ mixedSingletons.card + mixedMatching.card = Omega binaryHeawood ∧ (mixedSingletons.filter (fun v => heawoodColor v = false)).card = 3 ∧ (mixedSingletons.filter (fun v => heawoodColor v = true)).card = 3.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/HeawoodRepresentatives.binaryHeawood`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/HeawoodRepresentatives.heawood_parameters`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/HeawoodRepresentatives.mixedMatching`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/HeawoodRepresentatives.mixedSingletons`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/HeawoodRepresentatives.mixed_support_optimum`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodIncidence](../StarForming/HeawoodIncidence.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters](../StarForming/HeawoodParameters.md)
- Dependency: [D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds](C4RepresentativeBounds.md)
