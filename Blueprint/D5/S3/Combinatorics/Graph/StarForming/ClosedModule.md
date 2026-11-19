# Actual sixty-two-vertex module accounting

## Abstract

Actual sixty-two-vertex module accounting

The actual disjoint core and three broken-Heawood blocks partition sixty-two vertices. Restricting any actual dissociation selection gives the local omission inequality. Every saturated eight-block omits its own designated pair, and the three distinct omission budgets yield the unconditional module cap thirty-three. No restriction is imposed on either open interface vertex.

**Definition 1.1 (neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.neighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.neighbors` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def neighbors : Fin 62 → List (Fin 62).

**Definition 1.2 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph : SimpleGraph (Fin 62).

**Definition 1.3 (partition).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.partition`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.partition` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def partition : Fin 62 ≃ (Fin 20 ⊕ (Fin 3 × Fin 14)).

**Definition 1.4 (core).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.core`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.core` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def core (v : Fin 20) : Fin 62.

**Definition 1.5 (block).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.block`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.block` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def block (j : Fin 3) (v : Fin 14) : Fin 62.

**Definition 1.6 (coreSlice).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.coreSlice`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.coreSlice` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def coreSlice (D : Finset (Fin 62)) : Finset (Fin 20).

**Definition 1.7 (blockSlice).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.blockSlice`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.blockSlice` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def blockSlice (D : Finset (Fin 62)) (j : Fin 3) : Finset (Fin 14).

**Theorem 1.8 (card fibers).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.card_fibers`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.card_fibers` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem card_fibers {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (S : Finset (A × B)) : S.card=∑ a : A, (Finset.univ.filter (fun b => (a,b)∈S)).card.

**Theorem 1.9 (card slices).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.card_slices`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.card_slices` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem card_slices (D : Finset (Fin 62)) : D.card=(coreSlice D).card+∑ j : Fin 3, (blockSlice D j).card.

**Definition 1.10 (evenPort).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.evenPort`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.evenPort` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def evenPort (j : Fin 3) : Fin 20.

**Definition 1.11 (oddPort).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.oddPort`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.oddPort` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def oddPort (j : Fin 3) : Fin 20.

**Theorem 1.12 (saturated omission).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.saturated_omission`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.saturated_omission` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem saturated_omission (D : Finset (Fin 62)) (hD : IsKIndependent graph 2 D) (j : Fin 3) (h8 : (blockSlice D j).card=8) : evenPort j∉coreSlice D ∧ oddPort j∉coreSlice D.

**Theorem 1.13 (beta cap).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.beta_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.beta_cap` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_cap (D : Finset (Fin 62)) (hD : IsKIndependent graph 2 D) : D.card≤33.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.beta_cap`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.block`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.blockSlice`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.card_fibers`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.card_slices`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.core`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.coreSlice`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.evenPort`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.neighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.oddPort`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.partition`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedModule.saturated_omission`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/ClosedCore](ClosedCore.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/RegularCompensation](RegularCompensation.md)
