# Running Intersection Necessity

## Abstract

The three-node path with scopes {x}, {y}, {x} has matching edge images and no global row.

**Definition 1.1 (The assertion of sufficiency without RI).**

$$\forall T, S, Gamma, \operatorname{IsTree}\left(T\right) \land \operatorname{NonemptyLocalRelations}\left(Gamma\right) \land \operatorname{EdgeProjectionConsistency}\left(T, S, Gamma\right) \to \operatorname{Nonempty}\left(J\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Gluing/RunningIntersectionNecessity.EdgeMatchingSufficesWithoutRI` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The closed assertion quantifies over graphs on Fin 3, scopes in Fin 2, and local relations of dependent assignments with constant value type Fin 2. It says that a tree with nonempty local relations and equal complete edge projection images has a nonempty raw global join.

**Theorem 1.2 (A single variable receives contradictory values).**

$$\neg EdgeMatchingSufficesWithoutRI$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/RunningIntersectionNecessity.edge_matching_without_ri_is_false` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the path 0-1-2, variables x = 0 and y = 1, and scopes {x}, {y}, {x}. The three relations are singletons containing the rows x = 0, y = 0, and x = 1. Each relation is nonempty. Both edge separators are empty, so both complete projection images are the singleton empty assignment.

A global row would restrict to x = 0 at node 0 and x = 1 at node 2. These evaluate the same global coordinate, contradicting 0 unequal to 1 in Fin 2. The x occurrences are disconnected. Consequently complete edge consistency is insufficient without RI.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Gluing/RunningIntersectionNecessity.EdgeMatchingSufficesWithoutRI`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/RunningIntersectionNecessity.edge_matching_without_ri_is_false`
- Dependency: [D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords](RunningIntersectionRecords.md)
