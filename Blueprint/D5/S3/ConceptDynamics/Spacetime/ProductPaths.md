# Generated Product Causality

## Abstract

Generated Product Causality.

**Definition 1.1 (Only copied and parent edges generate causality).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ProductPaths.Edge`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/ProductPaths.Edge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The generating relation has precisely four constructors: copied left edges, copied right edges, and one edge from each parent to its generated child. Generated vertices have no outgoing generating edge.

**Theorem 1.2 (A path ending in an old component reflects old order).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ProductPaths.path_to_left`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ProductPaths.path_to_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The predecessor component invariant is proved by induction on a nonempty path. Each last edge entering an old component has its predecessor there, and the original strict relation composes. The right-component theorem is symmetric. This invariant is used by the actual archive embeddings.

**Theorem 1.3 (Frozen strict-coordinate results prove path legality).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ProductPaths.path_time`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ProductPaths.path_time` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two-parent maximum plus one makes each generating edge increase integer time. The frozen strict-coordinate path and acyclicity theorems apply directly. A separate path characterization identifies a generated event's ancestors as its parents and their old predecessors.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ProductPaths.Edge`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ProductPaths.path_time`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ProductPaths.path_to_left`
- Dependency: [D5/S3/ConceptDynamics/DagSemantics/ConservativeDagEmbedding](../DagSemantics/ConservativeDagEmbedding.md)
- Dependency: [D5/S3/ConceptDynamics/DagSemantics/StrictDependencyCoordinate](../DagSemantics/StrictDependencyCoordinate.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/ProductNodes](ProductNodes.md)
