# All-size triple-port ring parameters

## Abstract

All-size triple-port ring parameters

For every finite index permutation, including empty and singleton cases, the actual forty-eight-vertex fibers joined at ports sixteen and seventeen form a cubic bipartite graph with beta two equal to twenty-six per fiber and SF two equal to twenty-eight per fiber. The original attaining selections and exact finite fiber counts supply both lower bounds; the regular compensation upper bound supplies SF. Connectivity is proved separately.

**Definition 1.1 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleRings.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/TripleRings.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph (e : Equiv.Perm I) : SimpleGraph (I × Fin 48).

**Definition 1.2 (neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleRings.neighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/TripleRings.neighbors` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def neighbors (e : Equiv.Perm I) (v : I × Fin 48) : List (I × Fin 48).

**Theorem 1.3 (regular).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleRings.regular`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/TripleRings.regular` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem regular (e : Equiv.Perm I) : ∀ v, DegreeCapacity.degree (graph e) v=3.

**Theorem 1.4 (bipartite).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleRings.bipartite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/TripleRings.bipartite` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem bipartite (e : Equiv.Perm I) : (graph e).Colorable 2.

**Definition 1.5 (slice).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleRings.slice`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/TripleRings.slice` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def slice (S : Finset (I × Fin 48)) (i : I) : Finset (Fin 48).

**Theorem 1.6 (beta upper).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleRings.beta_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/TripleRings.beta_upper` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_upper (e : Equiv.Perm I) : beta (graph e) 2≤26*Fintype.card I.

**Theorem 1.7 (beta lower).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleRings.beta_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/TripleRings.beta_lower` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_lower (e : Equiv.Perm I) : 26*Fintype.card I≤beta (graph e) 2.

**Theorem 1.8 (sf lower).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleRings.sf_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/TripleRings.sf_lower` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem sf_lower (e : Equiv.Perm I) : 28*Fintype.card I≤SF (graph e) 2.

**Theorem 1.9 (parameters).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleRings.parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/TripleRings.parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem parameters (e : Equiv.Perm I) : Fintype.card (I × Fin 48)=48*Fintype.card I ∧ beta (graph e) 2=26*Fintype.card I ∧ SF (graph e) 2=28*Fintype.card I ∧ SF (graph e) 2-beta (graph e) 2=2*Fintype.card I.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleRings.beta_lower`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleRings.beta_upper`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleRings.bipartite`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleRings.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleRings.neighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleRings.parameters`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleRings.regular`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleRings.sf_lower`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleRings.slice`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses](TripleWitnesses.md)
