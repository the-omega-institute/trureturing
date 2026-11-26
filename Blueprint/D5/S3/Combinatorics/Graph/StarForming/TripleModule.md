# Actual triple-port core and disjoint block accounting

## Abstract

Actual triple-port core and disjoint block accounting

The original forty-eight-vertex module consists of its twenty-vertex core and two broken Heawood blocks attached to distinct prescribed ports. The stronger closed-core omission theorem applies after deleting one core edge. Exact disjoint slice counts and the two actual saturated-block omission charges bound every dissociation selection by twenty-six.

**Definition 1.1 (neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.neighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/TripleModule.neighbors` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def neighbors : Fin 48 → List (Fin 48).

**Definition 1.2 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/TripleModule.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph : SimpleGraph (Fin 48).

**Definition 1.3 (partition).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.partition`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/TripleModule.partition` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def partition : Fin 48 ≃ (Fin 20 ⊕ (Fin 2 × Fin 14)).

**Definition 1.4 (core).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.core`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/TripleModule.core` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def core (v : Fin 20) : Fin 48.

**Definition 1.5 (block).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.block`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/TripleModule.block` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def block (j : Fin 2) (v : Fin 14) : Fin 48.

**Definition 1.6 (coreSlice).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.coreSlice`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/TripleModule.coreSlice` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def coreSlice (D : Finset (Fin 48)) : Finset (Fin 20).

**Definition 1.7 (blockSlice).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.blockSlice`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/TripleModule.blockSlice` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def blockSlice (D : Finset (Fin 48)) (j : Fin 2) : Finset (Fin 14).

**Theorem 1.8 (card fibers).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.card_fibers`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/TripleModule.card_fibers` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem card_fibers {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (S : Finset (A × B)) : S.card=∑ a : A, (Finset.univ.filter (fun b => (a,b)∈S)).card.

**Theorem 1.9 (card slices).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.card_slices`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/TripleModule.card_slices` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem card_slices (D : Finset (Fin 48)) : D.card=(coreSlice D).card+∑ j : Fin 2, (blockSlice D j).card.

**Definition 1.10 (evenPort).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.evenPort`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/TripleModule.evenPort` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def evenPort (j : Fin 2) : Fin 20.

**Definition 1.11 (oddPort).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.oddPort`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/TripleModule.oddPort` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def oddPort (j : Fin 2) : Fin 20.

**Theorem 1.12 (saturated omission).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.saturated_omission`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/TripleModule.saturated_omission` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem saturated_omission (D : Finset (Fin 48)) (hD : IsKIndependent graph 2 D) (j : Fin 2) (h8 : (blockSlice D j).card=8) : evenPort j∉coreSlice D ∧ oddPort j∉coreSlice D.

**Theorem 1.13 (beta cap).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.beta_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/TripleModule.beta_cap` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_cap (D : Finset (Fin 48)) (hD : IsKIndependent graph 2 D) : D.card≤26.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.beta_cap`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.block`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.blockSlice`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.card_fibers`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.card_slices`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.core`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.coreSlice`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.evenPort`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.neighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.oddPort`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.partition`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleModule.saturated_omission`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/ClosedCore](ClosedCore.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/RegularCompensation](RegularCompensation.md)
