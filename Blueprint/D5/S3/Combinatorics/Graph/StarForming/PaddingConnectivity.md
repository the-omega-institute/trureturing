# Two-connectivity of independently sized padding modules and rings

## Abstract

Two-connectivity of independently sized padding modules and rings

The actual twenty-vertex unmarked core and thirty-four-vertex marked fiber have checked vertex-deletion paths. The projection records each actual fiber, including independently varying core types. Its symbolic transitive-permutation proof gives connectivity and connectivity after every vertex deletion for each positive module and each positive cyclic ring. Singleton restoration and independently varying positive core sizes remain in scope; no finite list of sizes replaces this proof.

**Theorem 1.1 (core parent facts).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingConnectivity.core_parent_facts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingConnectivity.core_parent_facts` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem core_parent_facts : ∀ z a : Fin 20, a≠z → core_parent z a≠z ∧ (a=core_root z ∨ coreGraph.Adj a (core_parent z a) ∧ core_rank z (core_parent z a)<core_rank z a).

**Theorem 1.2 (marked parent facts).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingConnectivity.marked_parent_facts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingConnectivity.marked_parent_facts` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem marked_parent_facts : ∀ z a : Fin 34, a≠z → marked_parent z a≠z ∧ (a=marked_root z ∨ markedGraph.Adj a (marked_parent z a) ∧ marked_rank z (marked_parent z a)<marked_rank z a).

**Theorem 1.3 (mapped deleted reachable).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingConnectivity.mapped_deleted_reachable`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingConnectivity.mapped_deleted_reachable` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem mapped_deleted_reachable {A V : Type*} (B : SimpleGraph A) (G : SimpleGraph V) (hB : B.Preconnected) (hd : ∀ z, (B.induce {a | a≠z}).Preconnected) (f : A ↪ V) (hf : ∀ a b, B.Adj a b → G.Adj (f a) (f b)) (z : V) (a b : A) (ha : f a≠z) (hb : f b≠z) : (G.induce {x | x≠z}).Reachable ⟨f a,ha⟩ ⟨f b,hb⟩.

**Theorem 1.4 (module two connected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingConnectivity.module_two_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingConnectivity.module_two_connected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem module_two_connected (e : Equiv.Perm I) (mark : I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) : (graph e mark).Connected ∧ (∀ z : Vertex I, ((graph e mark).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (Vertex I).

**Theorem 1.5 (rings two connected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingConnectivity.rings_two_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingConnectivity.rings_two_connected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem rings_two_connected [Nonempty J] (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) (hq : ∀ j, ∀ a b, ∃ n : ℕ, (q j : K j → K j)^[n] a=b) (he : ∀ i j, ∃ n : ℕ, (e : J → J)^[n] i=j) : (PaddingRings.graph q mark e).Connected ∧ (∀ z : PaddingRings.Vertex K, ((PaddingRings.graph q mark e).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (PaddingRings.Vertex K).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingConnectivity.core_parent_facts`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingConnectivity.mapped_deleted_reachable`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingConnectivity.marked_parent_facts`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingConnectivity.module_two_connected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingConnectivity.rings_two_connected`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CyclicProjection](CyclicProjection.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/PaddingRings](PaddingRings.md)
