# Strict Dependency Coordinate

## Abstract

A strictly increasing dependency coordinate linearizes paths and forbids cycles.

**Theorem 1.1 (Strict coordinates increase along nonempty paths).**

$$\forall edge: V \to V \to Prop, coordinate: V \to Rank,\\{}[\operatorname{Preorder}\left(Rank\right)],\\{}\operatorname{StrictDependencyCoordinate}\left(edge, coordinate\right) \Rightarrow\\{}\forall first, last: V, \operatorname{TransGen}\left(edge, first, last\right) \Rightarrow \operatorname{coordinate}\left(first\right) < \operatorname{coordinate}\left(last\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/StrictDependencyCoordinate.strict_of_transGen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a preordered rank carrier, assume every dependency edge strictly increases a coordinate. A supplied nonempty dependency path then strictly increases its endpoint ranks.

The nonempty TransGen path is an explicit premise; no strict conclusion is claimed for a merely reflexive path.

**Theorem 1.2 (Strict coordinates forbid directed cycles).**

$$\forall edge: V \to V \to Prop, coordinate: V \to Rank,\\{}[\operatorname{Preorder}\left(Rank\right)],\\{}\operatorname{StrictDependencyCoordinate}\left(edge, coordinate\right) \Rightarrow\\{}\forall vertex: V, \neg \operatorname{TransGen}\left(edge, vertex, vertex\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/StrictDependencyCoordinate.acyclic_of_strictCoordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same strict-coordinate hypothesis, no vertex supports a nonempty dependency path back to itself.

The conclusion rules out TransGen self-cycles. It does not rule out the reflexive witness present in ReflTransGen.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagSemantics/StrictDependencyCoordinate.acyclic_of_strictCoordinate`
- Truth anchor: `D5/S3/ConceptDynamics/DagSemantics/StrictDependencyCoordinate.strict_of_transGen`
