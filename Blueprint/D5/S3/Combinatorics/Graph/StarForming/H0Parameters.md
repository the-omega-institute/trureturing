# Exact H0 cyclic degrees and edge counts

## Abstract

Exact H0 cyclic degrees and edge counts

The unchanged ten-vertex H0 table and actual additional cyclic port edge give exact degrees, edge count seventeen per cell, beta five per cell, SF six per cell and gap one per cell. The cyclic size is at least two, and both degree extrema are attained. The single-block edge restoration and the separate chain structure are not silently included in this edge-count statement.

**Definition 1.1 (neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/H0Parameters.neighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/H0Parameters.neighbors` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def neighbors (e : Equiv.Perm I) (v : I × Fin 10) : List (I × Fin 10).

**Theorem 1.2 (degrees).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/H0Parameters.degrees`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/H0Parameters.degrees` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem degrees (e : Equiv.Perm I) (hf : ∀ i,e i≠i) (v : I × Fin 10) : DegreeCapacity.degree (graph e) v= if v.2=2 ∨ v.2=7 then 2 else if v.2=1 ∨ v.2=6 then 3 else 4.

**Theorem 1.3 (edge count).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/H0Parameters.edge_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/H0Parameters.edge_count` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem edge_count (e : Equiv.Perm I) (hf : ∀ i,e i≠i) : (graph e).edgeFinset.card=17*Fintype.card I.

**Theorem 1.4 (cyclic parameters).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/H0Parameters.cyclic_parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/H0Parameters.cyclic_parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem cyclic_parameters (r : ℕ) (hr : 2≤r) : let G.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/H0Parameters.cyclic_parameters`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/H0Parameters.degrees`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/H0Parameters.edge_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/H0Parameters.neighbors`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity](DegreeCapacity.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/H0Geometry](H0Geometry.md)
