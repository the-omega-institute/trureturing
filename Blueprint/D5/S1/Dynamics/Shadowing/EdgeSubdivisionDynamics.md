# Exactness and expansion from closed edge subdivisions

## Abstract

Exactness and expansion from closed edge subdivisions

**Theorem 1.1 (Contracting inverse charts give exactness).**

Lean statement: `D5/S1/Dynamics/Shadowing/EdgeSubdivisionDynamics.topologicallyExact_of_inverse_charts`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/EdgeSubdivisionDynamics.topologicallyExact_of_inverse_charts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pull a contracting branch through a prescribed point at each iterate. The branch eventually fits inside the given open set while its image covers a whole edge. The next iterate covers the carrier.

**Theorem 1.2 (Finite compact cells give a uniform expansion scale).**

Lean statement: `D5/S1/Dynamics/Shadowing/EdgeSubdivisionDynamics.forwardBowenBound_one_of_compact_cells`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/EdgeSubdivisionDynamics.forwardBowenBound_one_of_compact_cells` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Disjoint compact cells have a common positive lower bound on separation. Along an orbit pair lying below that scale, intersecting cells force exponential growth of the distance, hence every sufficiently small forward Bowen set is a singleton.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/EdgeSubdivisionDynamics.forwardBowenBound_one_of_compact_cells`
- Truth anchor: `D5/S1/Dynamics/Shadowing/EdgeSubdivisionDynamics.topologicallyExact_of_inverse_charts`
- Dependency: [D5/S1/Dynamics/Shadowing/ExactPendantObstruction](ExactPendantObstruction.md)
