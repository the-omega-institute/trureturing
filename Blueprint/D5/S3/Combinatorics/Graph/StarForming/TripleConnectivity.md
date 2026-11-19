# All-positive-length triple-port two-connectivity

## Abstract

All-positive-length triple-port two-connectivity

Actual checked local vertex-deletion paths and the sixteen-to-seventeen bridge combine with the symbolic orbit argument. For every positive cyclic length the actual triple-port assembly is connected and remains connected after deleting any vertex. The proof includes lengths one and two.

**Theorem 1.1 (two connected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleConnectivity.two_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/TripleConnectivity.two_connected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem two_connected [Nonempty I] (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) : (graph e).Connected ∧ (∀ z : I × Fin 48, ((graph e).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (I × Fin 48).

**Theorem 1.2 (cyclic two connected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleConnectivity.cyclic_two_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/TripleConnectivity.cyclic_two_connected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem cyclic_two_connected (r : ℕ) (hr : 0<r) : (graph (finRotate r)).Connected ∧ (∀ z : Fin r × Fin 48, ((graph (finRotate r)).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (Fin r × Fin 48).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleConnectivity.cyclic_two_connected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleConnectivity.two_connected`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CyclicConnectivity](CyclicConnectivity.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/TripleRings](TripleRings.md)
