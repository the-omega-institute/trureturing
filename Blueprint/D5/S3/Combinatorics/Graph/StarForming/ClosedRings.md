# Exact parameters of arbitrary finite closed-high rings

## Abstract

Exact parameters of arbitrary finite closed-high rings

A permutation on an arbitrary finite index type links the actual sixty-two-vertex modules. Slice accounting gives beta thirty-three per module; actual attaining selections and outside-only rewiring give SF thirty-six per module. The graph is cubic bipartite, including the empty family and singleton restoration. Connectivity and one-vertex-deletion connectivity require their own orbit argument and are not supplied by the parameter equalities.

**Definition 1.1 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph (e : Equiv.Perm I) : SimpleGraph (I × Fin 62).

**Definition 1.2 (neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.neighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.neighbors` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def neighbors (e : Equiv.Perm I) (v : I × Fin 62) : List (I × Fin 62).

**Theorem 1.3 (regular).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.regular`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.regular` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem regular (e : Equiv.Perm I) : ∀ v, DegreeCapacity.degree (graph e) v=3.

**Theorem 1.4 (bipartite).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.bipartite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.bipartite` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem bipartite (e : Equiv.Perm I) : (graph e).Colorable 2.

**Definition 1.5 (slice).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.slice`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.slice` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def slice (S : Finset (I × Fin 62)) (i : I) : Finset (Fin 62).

**Theorem 1.6 (beta upper).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.beta_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.beta_upper` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_upper (e : Equiv.Perm I) : beta (graph e) 2≤33*Fintype.card I.

**Theorem 1.7 (beta lower).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.beta_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.beta_lower` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_lower (e : Equiv.Perm I) : 33*Fintype.card I≤beta (graph e) 2.

**Theorem 1.8 (sf lower).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.sf_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.sf_lower` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem sf_lower (e : Equiv.Perm I) : 36*Fintype.card I≤SF (graph e) 2.

**Theorem 1.9 (parameters).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem parameters (e : Equiv.Perm I) : Fintype.card (I × Fin 62)=62*Fintype.card I ∧ beta (graph e) 2=33*Fintype.card I ∧ SF (graph e) 2=36*Fintype.card I ∧ SF (graph e) 2-beta (graph e) 2=3*Fintype.card I.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.beta_lower`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.beta_upper`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.bipartite`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.neighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.parameters`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.regular`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.sf_lower`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedRings.slice`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses](ClosedRingWitnesses.md)
