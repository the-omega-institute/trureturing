# All-degree two-connectivity of the sharp positive-gap graphs

## Abstract

All-degree two-connectivity of the sharp positive-gap graphs

The actual high crown is connected after every vertex deletion by explicit short paths, including a detour when a common opposite high is the deleted vertex. The actual disjoint high--outside--outside--high ears and the two hubs each retain a path into that crown. For every finite index permutation with no fixed point and no two-step fixed point this proves two-connectivity. The cyclic specialization includes every degree at least three, without enumerating graph orders. The separate rings of broken sharp blocks still need their own source integration.

**Theorem 1.1 (delete preconnected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SharpRegularConnectivity.delete_preconnected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SharpRegularConnectivity.delete_preconnected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem delete_preconnected (next : Equiv.Perm I) (hd : 3 ≤ Fintype.card I) (h1 : ∀ i, next i ≠ i) (h2 : ∀ i, next (next i) ≠ i) (z : Vertex I) : ((graph next).induce {v | v ≠ z}).Preconnected.

**Theorem 1.2 (two connected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SharpRegularConnectivity.two_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SharpRegularConnectivity.two_connected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem two_connected (next : Equiv.Perm I) (hd : 3 ≤ Fintype.card I) (h1 : ∀ i, next i ≠ i) (h2 : ∀ i, next (next i) ≠ i) : (graph next).Connected ∧ (∀ z : Vertex I, ((graph next).induce {v | v ≠ z}).Connected) ∧ 3 ≤ Fintype.card (Vertex I).

**Theorem 1.3 (cyclic two connected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SharpRegularConnectivity.cyclic_two_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SharpRegularConnectivity.cyclic_two_connected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem cyclic_two_connected (d : ℕ) (hd : 3 ≤ d) : (graph (finRotate d)).Connected ∧ (∀ z : Vertex (Fin d), ((graph (finRotate d)).induce {v | v ≠ z}).Connected) ∧ 3 ≤ Fintype.card (Vertex (Fin d)).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SharpRegularConnectivity.cyclic_two_connected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SharpRegularConnectivity.delete_preconnected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SharpRegularConnectivity.two_connected`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/FiberConnectivity](FiberConnectivity.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/SharpRegular](SharpRegular.md)
