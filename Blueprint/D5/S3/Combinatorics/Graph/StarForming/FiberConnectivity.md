# Connectivity through actual connected fibers

## Abstract

Connectivity through actual connected fibers

Actual inter-fiber edges and connected fibers lift preconnectedness from an arbitrary base graph. Two disjoint endpoint pairs survive every one-vertex deletion, and a strictly decreasing parent rank supplies actual paths to a root. These lemmas are consumed by the reciprocal Heawood assembly.

**Theorem 1.1 (preconnected of fibers).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FiberConnectivity.preconnected_of_fibers`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/FiberConnectivity.preconnected_of_fibers` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem preconnected_of_fibers {V I : Type*} (G : SimpleGraph V) (Q : SimpleGraph I) (f : V → I) (hQ : Q.Preconnected) (hf : ∀ a b, f a = f b → G.Reachable a b) (he : ∀ i j, Q.Adj i j → ∃ a b, f a = i ∧ f b = j ∧ G.Adj a b) : G.Preconnected.

**Theorem 1.2 (surviving pair).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FiberConnectivity.surviving_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/FiberConnectivity.surviving_pair` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem surviving_pair {V : Type*} (a b c d z : V) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) : (a ≠ z ∧ b ≠ z) ∨ (c ≠ z ∧ d ≠ z).

**Theorem 1.3 (preconnected of rank).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FiberConnectivity.preconnected_of_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/FiberConnectivity.preconnected_of_rank` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem preconnected_of_rank {V : Type*} (G : SimpleGraph V) (root : V) (parent : V → V) (rank : V → ℕ) (hstep : ∀ v, v ≠ root → G.Adj v (parent v) ∧ rank (parent v) < rank v) : G.Preconnected.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FiberConnectivity.preconnected_of_fibers`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FiberConnectivity.preconnected_of_rank`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FiberConnectivity.surviving_pair`
