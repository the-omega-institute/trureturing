# Actual augmented bipartite exchanges

## Abstract

Actual augmented bipartite exchanges

For every actual minimal two-star-forming selection in a finite bipartite graph, chosen high witnesses and additional unreserved-leaf witnesses form one injective outside map. The two explicit exchange selections are canonical dissociation sets. Their cardinalities plus the actual selected isolate count equal twice the selected size. Consequently 2|S|<=2 beta plus selected isolates, without a regularity, connectivity or nonempty assumption. Empty high/leaf classes and disconnected graphs remain in scope.

**Definition 1.1 (Isolate).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.Isolate`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.Isolate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact declaration: def Isolate (v : V) : Prop.

**Definition 1.2 (LeafAt).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.LeafAt`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.LeafAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact declaration: def LeafAt (u h : V) : Prop.

**Theorem 1.3 (witness failure).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.witness_failure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.witness_failure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem witness_failure (hS : IsMinimalStarForming G 2 S) (v : V) (hv : High G.Adj (· ∈ S) v) : Failure G.Adj (· ∈ S) v (witness G S hS v).

**Theorem 1.4 (witness injective).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.witness_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.witness_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem witness_injective (hS : IsMinimalStarForming G 2 S) (v w : V) (hv : High G.Adj (· ∈ S) v) (hw : High G.Adj (· ∈ S) w) (he : witness G S hS v = witness G S hS w) : v = w.

**Theorem 1.5 (adjacent other isolate).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.adjacent_other_isolate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.adjacent_other_isolate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem adjacent_other_isolate (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (h x y : V) (hf : Failure G.Adj (· ∈ S) h x) (hxh : G.Adj x h) (hy : y ∈ S) (hne : y ≠ h) (hxy : G.Adj x y) : Isolate G S y.

**Theorem 1.6 (nonadjacent leaf).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.nonadjacent_leaf`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.nonadjacent_leaf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem nonadjacent_leaf (hS : IsMinimalStarForming G 2 S) (h x : V) (hh : High G.Adj (· ∈ S) h) (hf : Failure G.Adj (· ∈ S) h x) (hne : ¬ G.Adj x h) : ∃ u, LeafAt G S u h ∧ G.Adj x u ∧ ∀ w ∈ S, G.Adj x w → w = u.

**Theorem 1.7 (leaf support unique).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.leaf_support_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.leaf_support_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem leaf_support_unique (u h k : V) (hh : LeafAt G S u h) (hk : LeafAt G S u k) : h = k.

**Theorem 1.8 (nonhigh unique).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.nonhigh_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.nonhigh_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem nonhigh_unique (v x y : V) (hv : v ∈ S) (hn : ¬ High G.Adj (· ∈ S) v) (hx : x ∈ S) (hy : y ∈ S) (hax : G.Adj v x) (hay : G.Adj v y) : x = y.

**Definition 1.9 (Reserved).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.Reserved`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.Reserved` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact declaration: def Reserved (hS : IsMinimalStarForming G 2 S) (u : V) : Prop.

**Definition 1.10 (Extra).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.Extra`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.Extra` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact declaration: def Extra (hS : IsMinimalStarForming G 2 S) (u : V) : Prop.

**Definition 1.11 (Active).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.Active`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.Active` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact declaration: def Active (hS : IsMinimalStarForming G 2 S) (u : V) : Prop.

**Definition 1.12 (Passive).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.Passive`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.Passive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact declaration: def Passive (hS : IsMinimalStarForming G 2 S) (u : V) : Prop.

**Theorem 1.13 (leaf not high).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.leaf_not_high`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.leaf_not_high` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem leaf_not_high (u h : V) (hu : LeafAt G S u h) : ¬ High G.Adj (· ∈ S) u.

**Theorem 1.14 (reserved leaf).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.reserved_leaf`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.reserved_leaf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem reserved_leaf (hS : IsMinimalStarForming G 2 S) (u : V) (hu : Reserved G S hS u) : ∃ h, LeafAt G S u h ∧ ¬ G.Adj (witness G S hS h) h ∧ G.Adj (witness G S hS h) u.

**Theorem 1.15 (extra has failure).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.extra_has_failure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.extra_has_failure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem extra_has_failure (hS : IsMinimalStarForming G 2 S) (u : V) (hu : Extra G S hS u) : ∃ x, Failure G.Adj (· ∈ S) u x ∧ G.Adj x u.

**Theorem 1.16 (active failure).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.active_failure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.active_failure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem active_failure (hS : IsMinimalStarForming G 2 S) (u : V) (hu : Active G S hS u) : Failure G.Adj (· ∈ S) u (activeWitness G S hS u).

**Theorem 1.17 (active selected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.active_selected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.active_selected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem active_selected (hS : IsMinimalStarForming G 2 S) (u : V) (hu : Active G S hS u) : u ∈ S.

**Theorem 1.18 (active not isolate).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.active_not_isolate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.active_not_isolate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem active_not_isolate (hS : IsMinimalStarForming G 2 S) (u : V) (hu : Active G S hS u) : ¬ Isolate G S u.

**Theorem 1.19 (extra witness adjacent).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.extra_witness_adjacent`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.extra_witness_adjacent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem extra_witness_adjacent (hS : IsMinimalStarForming G 2 S) (u : V) (hu : Extra G S hS u) : G.Adj (activeWitness G S hS u) u.

**Theorem 1.20 (reserved passive).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.reserved_passive`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.reserved_passive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem reserved_passive (hS : IsMinimalStarForming G 2 S) (u : V) (hu : Reserved G S hS u) : Passive G S hS u.

**Theorem 1.21 (active shape).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.active_shape`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.active_shape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem active_shape (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hS : IsMinimalStarForming G 2 S) (a v : V) (ha : Active G S hS a) (hv : v ∈ S) (hxv : G.Adj (activeWitness G S hS a) v) : Isolate G S v ∨ v = a ∨ (Passive G S hS v ∧ G.Adj a v).

**Theorem 1.22 (activeWitness injective).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.activeWitness_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.activeWitness_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem activeWitness_injective (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hS : IsMinimalStarForming G 2 S) (a b : V) (ha : Active G S hS a) (hb : Active G S hS b) (heq : activeWitness G S hS a = activeWitness G S hS b) : a = b.

**Theorem 1.23 (active passive edges).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.active_passive_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.active_passive_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem active_passive_edges (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hS : IsMinimalStarForming G 2 S) (a b : V) (ha : Active G S hS a) (hb : Passive G S hS b) : G.Adj a b ↔ G.Adj (activeWitness G S hS a) b.

**Theorem 1.24 (active passive unique).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.active_passive_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.active_passive_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem active_passive_unique (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hS : IsMinimalStarForming G 2 S) (a b c : V) (ha : Active G S hS a) (hb : Passive G S hS b) (hc : Passive G S hS c) (hab : G.Adj a b) (hac : G.Adj a c) : b = c.

**Theorem 1.25 (exchange dissociation).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.exchange_dissociation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.exchange_dissociation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem exchange_dissociation (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hS : IsMinimalStarForming G 2 S) (c : Bool) : IsKIndependent G 2 (exchange G S hS color c).

**Theorem 1.26 (exchange card sum).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.exchange_card_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.exchange_card_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem exchange_card_sum (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hS : IsMinimalStarForming G 2 S) : (exchange G S hS color false).card + (exchange G S hS color true).card + (DegreeCapacity.isolates G S).card = 2 * S.card.

**Theorem 1.27 (selection compensation).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.selection_compensation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.selection_compensation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem selection_compensation (hG : G.Colorable 2) (S : Finset V) (hS : IsMinimalStarForming G 2 S) : 2 * S.card ≤ 2 * beta G 2 + (DegreeCapacity.isolates G S).card.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.Active`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.Extra`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.Isolate`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.LeafAt`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.Passive`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.Reserved`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.activeWitness_injective`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.active_failure`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.active_not_isolate`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.active_passive_edges`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.active_passive_unique`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.active_selected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.active_shape`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.adjacent_other_isolate`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.exchange_card_sum`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.exchange_dissociation`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.extra_has_failure`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.extra_witness_adjacent`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.leaf_not_high`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.leaf_support_unique`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.nonadjacent_leaf`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.nonhigh_unique`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.reserved_leaf`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.reserved_passive`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.selection_compensation`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.witness_failure`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.witness_injective`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/BipartiteBounds](BipartiteBounds.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CubicPathAccounting](CubicPathAccounting.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity](DegreeCapacity.md)
