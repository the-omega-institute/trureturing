# Cyclic connectivity for independently varying fibers

## Abstract

Cyclic connectivity for independently varying fibers

An actual projection partitions vertices into possibly different fiber types and sizes. Actual entrance and exit vertices and one cyclic bridge per index join connected fibers. After any vertex deletion, local surviving-fiber reachability and distinct entrance and exit ports allow one of the two cyclic directions to reach the deleted fiber. The argument is symbolic over a transitive permutation; it enumerates no graph orders.

**Theorem 1.1 (preconnected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CyclicProjection.preconnected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CyclicProjection.preconnected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem preconnected (G : SimpleGraph V) (f : V → I) (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) (p q : I → V) (hp : ∀ i, f (p i)=i) (hq : ∀ i, f (q i)=i) (hlocal : ∀ a b, f a=f b → G.Reachable a b) (hbridge : ∀ i, G.Adj (p i) (q (e i))) : G.Preconnected.

**Theorem 1.2 (delete preconnected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CyclicProjection.delete_preconnected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CyclicProjection.delete_preconnected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem delete_preconnected (G : SimpleGraph V) (f : V → I) (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) (p q : I → V) (hp : ∀ i, f (p i)=i) (hq : ∀ i, f (q i)=i) (hne : ∀ i, p i≠q i) (z : V) (hlocal : ∀ a b : {x : V // x≠z}, f a.val=f b.val → (G.induce {x | x≠z}).Reachable a b) (hbridge : ∀ i, G.Adj (p i) (q (e i))) : (G.induce {x | x≠z}).Preconnected.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CyclicProjection.delete_preconnected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CyclicProjection.preconnected`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CyclicConnectivity](CyclicConnectivity.md)
