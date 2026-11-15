# Actual cyclic bridges and vertex-deleted fibers

## Abstract

Actual cyclic bridges and vertex-deleted fibers

Local actual graph paths and a transitive permutation give full connectivity. With distinct bridge ports and each local vertex deletion connected, an appropriate forward or inverse cyclic route avoids the deleted bridge endpoint. This general path lemma is consumed by the actual H0 and long-core family proofs.

**Theorem 1.1 (preconnected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CyclicConnectivity.preconnected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CyclicConnectivity.preconnected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem preconnected (G : SimpleGraph (I × A)) (B : SimpleGraph A) (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) (p q : A) (hB : B.Preconnected) (hint : ∀ i a b, B.Adj a b → G.Adj (i,a) (i,b)) (hbridge : ∀ i, G.Adj (i,p) (e i,q)) : G.Preconnected.

**Theorem 1.2 (delete preconnected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CyclicConnectivity.delete_preconnected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CyclicConnectivity.delete_preconnected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem delete_preconnected (G : SimpleGraph (I × A)) (B : SimpleGraph A) (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) (p q : A) (hpq : p≠q) (hB : B.Preconnected) (hdelete : ∀ z : A, (B.induce {a | a≠z}).Preconnected) (hint : ∀ i a b, B.Adj a b → G.Adj (i,a) (i,b)) (hbridge : ∀ i, G.Adj (i,p) (e i,q)) (z : I × A) : (G.induce {x | x≠z}).Preconnected.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CyclicConnectivity.delete_preconnected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CyclicConnectivity.preconnected`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/FiberConnectivity](FiberConnectivity.md)
