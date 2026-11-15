# Actual H0 cyclic two-connectivity

## Abstract

Actual H0 cyclic two-connectivity

The original unchanged H0 graph has checked local parent/rank path certificates after every vertex deletion. Its actual port bridge and symbolic transitive index permutation give connectivity and connectivity after every vertex deletion. All positive cyclic lengths are included; exact seventeen-edge counting separately excludes the singleton restored-edge case.

**Definition 1.1 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/H0Geometry.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/H0Geometry.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph {I : Type} (e : Equiv.Perm I) : SimpleGraph (I × Fin 10).

**Theorem 1.2 (two connected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/H0Geometry.two_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/H0Geometry.two_connected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem two_connected [Nonempty I] (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) : (graph e).Connected ∧ (∀ z : I × Fin 10, ((graph e).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (I × Fin 10).

**Theorem 1.3 (cyclic two connected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/H0Geometry.cyclic_two_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/H0Geometry.cyclic_two_connected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem cyclic_two_connected (r : ℕ) (hr : 0<r) : (graph (finRotate r)).Connected ∧ (∀ z : Fin r × Fin 10, ((graph (finRotate r)).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (Fin r × Fin 10).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/H0Geometry.cyclic_two_connected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/H0Geometry.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/H0Geometry.two_connected`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CyclicConnectivity](CyclicConnectivity.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Semantics](Semantics.md)
