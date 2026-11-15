# Internal clauses at a boundary port

## Abstract

Internal clauses at a boundary port

A clause based at a selected port includes the actual external neighbor when the graph and support conditions displayed in the theorem hold. The resulting support and private-ownership facts constrain the possible external sole-neighbor witness. The graph relation, internal set, selected set and boundary ports remain separate parameters.

**Definition 1.1 (BasedAt).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PortClauseOwnership.BasedAt`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PortClauseOwnership.BasedAt` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def BasedAt {Vertex : Type} (internal : Vertex → Prop) (port : Vertex) : Clause Vertex → Prop | .closed center => center = port | .oriented center neighbor => (center = port ∧ internal neighbor) ∨ (neighbor = port ∧ internal center) theorem external_neighbor_in_support {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (internal : Vertex → Prop) (port vertex : Vertex) (clause : Clause Vertex) (hbased : BasedAt internal port clause) (hexternal : ¬ internal vertex) (hedge : adjacency port vertex) : Support adjacency clause vertex.

**Theorem 1.2 (external neighbor in support).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PortClauseOwnership.external_neighbor_in_support`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PortClauseOwnership.external_neighbor_in_support` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem external_neighbor_in_support {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (internal : Vertex → Prop) (port vertex : Vertex) (clause : Clause Vertex) (hbased : BasedAt internal port clause) (hexternal : ¬ internal vertex) (hedge : adjacency port vertex) : Support adjacency clause vertex.

**Theorem 1.3 (outside neighbors unique).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PortClauseOwnership.outside_neighbors_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PortClauseOwnership.outside_neighbors_unique` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem outside_neighbors_unique {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (internal selection : Vertex → Prop) (port owner : Vertex) (clause : Clause Vertex) (hbased : BasedAt internal port clause) (hprivate : Private adjacency selection clause owner) : ∀ vertex, ¬ internal vertex → selection vertex → adjacency port vertex → vertex = owner.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PortClauseOwnership.BasedAt`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PortClauseOwnership.external_neighbor_in_support`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PortClauseOwnership.outside_neighbors_unique`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/PrivateClauses](PrivateClauses.md)
