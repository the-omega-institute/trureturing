# Local star witnesses and arbitrary H0 interfaces

## Abstract

Local star witnesses and arbitrary H0 interfaces

The same ten-vertex H0 data is reused from the canonical refutation. Interfaces are arbitrary directed relations on the block indices; no symmetry, connectivity, nonemptiness or distinct-block premise is imposed. Only ports 0 and 5 can acquire external edges. The chosen set is minimal for every interface, has six vertices per block, and admits a proper two-coloring. Cyclic attainment is separate from cyclic connectivity and edge counts.

**Definition 1.1 (TwoAt).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.TwoAt`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Amplification.TwoAt` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def TwoAt {V : Type*} (G : SimpleGraph V) (S : Set V) (x : V) : Prop.

**Definition 1.2 (Forms).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.Forms`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Amplification.Forms` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def Forms {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop.

**Definition 1.3 (Minimal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.Minimal`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Amplification.Minimal` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def Minimal {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop.

**Definition 1.4 (LiteralAt).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.LiteralAt`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Amplification.LiteralAt` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def LiteralAt {V : Type*} (G : SimpleGraph V) (S : Set V) (x : V) : Prop.

**Theorem 1.5 (literal iff local).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.literal_iff_local`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Amplification.literal_iff_local` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem literal_iff_local {V : Type*} (G : SimpleGraph V) (S : Set V) (x : V) (hx : x ∉ S) : LiteralAt G S x ↔ TwoAt G S x.

**Theorem 1.6 (twoAt mono).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.twoAt_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Amplification.twoAt_mono` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem twoAt_mono {V : Type*} (G : SimpleGraph V) {S T : Set V} (hST : S ⊆ T) {x : V} : TwoAt G S x → TwoAt G T x.

**Theorem 1.7 (minimal of deletion failures).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.minimal_of_deletion_failures`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Amplification.minimal_of_deletion_failures` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem minimal_of_deletion_failures {V : Type*} (G : SimpleGraph V) (S : Set V) (hforms : Forms G S) (hfail : ∀ selected ∈ S, ∃ x, x ∉ S \ {selected} ∧ ¬ TwoAt G (S \ {selected}) x) : Minimal G S.

**Definition 1.8 (baseEdges).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.baseEdges`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Amplification.baseEdges` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev baseEdges.

**Definition 1.9 (base).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.base`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Amplification.base` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev base.

**Definition 1.10 (selected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.selected`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Amplification.selected` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev selected.

**Definition 1.11 (failure).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.failure`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Amplification.failure` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def failure (vertex : Fin 10) : Fin 10.

**Definition 1.12 (Unported).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.Unported`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Amplification.Unported` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def Unported (vertex : Fin 10) : Prop.

**Definition 1.13 (family).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.family`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Amplification.family` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def family {I : Type*} (interfaces : I → I → Prop) : SimpleGraph (I × Fin 10).

**Definition 1.14 (chosen).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.chosen`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Amplification.chosen` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def chosen {I : Type*} : Set (I × Fin 10).

**Theorem 1.15 (adj unported).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.adj_unported`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Amplification.adj_unported` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem adj_unported {I : Type*} (interfaces : I → I → Prop) (first second : I × Fin 10) (hu : Unported first.2) : (family interfaces).Adj first second ↔ first.1 = second.1 ∧ base.Adj first.2 second.2.

**Theorem 1.16 (failure unported).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.failure_unported`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Amplification.failure_unported` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem failure_unported (vertex : Fin 10) (hs : vertex ∈ selected) : Unported (failure vertex).

**Theorem 1.17 (base failure).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.base_failure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Amplification.base_failure` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem base_failure (vertex : Fin 10) (hs : vertex ∈ selected) : failure vertex ∉ selected.erase vertex ∧ (∀ first ∈ selected.erase vertex, ∀ second ∈ selected.erase vertex, base.Adj (failure vertex) first → base.Adj (failure vertex) second → first = second) ∧ (∀ center ∈ selected.erase vertex, base.Adj (failure vertex) center → Unported center ∧ ∀ leaf ∈ selected.erase vertex, ¬ base.Adj center leaf).

**Theorem 1.18 (family forms).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.family_forms`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Amplification.family_forms` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem family_forms {I : Type*} (interfaces : I → I → Prop) : Forms (family interfaces) (chosen : Set (I × Fin 10)).

**Theorem 1.19 (family deletion failure).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.family_deletion_failure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Amplification.family_deletion_failure` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem family_deletion_failure {I : Type*} (interfaces : I → I → Prop) (block : I) (vertex : Fin 10) (hs : vertex ∈ selected) : (block, failure vertex) ∉ (chosen : Set (I × Fin 10)) \ {(block, vertex)} ∧ ¬ TwoAt (family interfaces) (chosen \ {(block, vertex)}) (block, failure vertex).

**Theorem 1.20 (family minimal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.family_minimal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Amplification.family_minimal` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem family_minimal {I : Type*} (interfaces : I → I → Prop) : Minimal (family interfaces) (chosen : Set (I × Fin 10)).

**Theorem 1.21 (chosen card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.chosen_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Amplification.chosen_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem chosen_card {I : Type*} [Fintype I] [DecidableEq I] : ((Finset.univ : Finset I).product selected).card = 6 * Fintype.card I.

**Theorem 1.22 (family bipartite).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.family_bipartite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Amplification.family_bipartite` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem family_bipartite {I : Type*} (interfaces : I → I → Prop) : (family interfaces).Colorable 2.

**Definition 1.23 (cycleGraph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.cycleGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Amplification.cycleGraph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def cycleGraph (copies : ℕ) : SimpleGraph (Fin copies × Fin 10).

**Definition 1.24 (cycleSelected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.cycleSelected`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Amplification.cycleSelected` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def cycleSelected (copies : ℕ) : Finset (Fin copies × Fin 10).

**Theorem 1.25 (cycle minimal card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Amplification.cycle_minimal_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Amplification.cycle_minimal_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem cycle_minimal_card (copies : ℕ) : Minimal (cycleGraph copies) (↑(cycleSelected copies) : Set (Fin copies × Fin 10)) ∧ (cycleSelected copies).card = 6 * copies ∧ (cycleGraph copies).Colorable 2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.Forms`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.LiteralAt`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.Minimal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.TwoAt`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.Unported`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.adj_unported`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.base`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.baseEdges`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.base_failure`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.chosen`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.chosen_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.cycleGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.cycleSelected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.cycle_minimal_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.failure`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.failure_unported`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.family`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.family_bipartite`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.family_deletion_failure`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.family_forms`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.family_minimal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.literal_iff_local`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.minimal_of_deletion_failures`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.selected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Amplification.twoAt_mono`
- Dependency: [D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation](../StarFormingDissociationRefutation.md)
