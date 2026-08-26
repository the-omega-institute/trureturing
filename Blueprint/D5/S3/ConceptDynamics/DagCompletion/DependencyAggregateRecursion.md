# Dependency Aggregate Recursion

## Abstract

Global prerequisite meet and join aggregates satisfy exact local predecessor recursion laws.

**Theorem 1.1 (Prerequisite joins satisfy local recursion).**

$$\forall edge: V \to V \to Prop, label: V \to Label, node: V,\\{}[\operatorname{CompleteLattice}\left(Label\right)],\\{}\operatorname{prerequisiteJoin}\left(edge, label, node\right) = \operatorname{sup}\left(\operatorname{label}\left(node\right), \operatorname{iSup}_{predecessor: V} \operatorname{iSup}_{dependency: \operatorname{edge}\left(predecessor, node\right)} \operatorname{prerequisiteJoin}\left(edge, label, predecessor\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/DependencyAggregateRecursion.prerequisiteJoin_recursion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a complete lattice, the global join over a node's prerequisite cone equals its own label joined with the joins of every direct predecessor.

The equality includes all direct predecessors through the displayed local aggregate; it does not assume finiteness or choose an enumeration.

**Theorem 1.2 (Prerequisite meets satisfy local recursion).**

$$\forall edge: V \to V \to Prop, label: V \to Label, node: V,\\{}[\operatorname{CompleteLattice}\left(Label\right)],\\{}\operatorname{prerequisiteMeet}\left(edge, label, node\right) = \operatorname{inf}\left(\operatorname{label}\left(node\right), \operatorname{iInf}_{predecessor: V} \operatorname{iInf}_{dependency: \operatorname{edge}\left(predecessor, node\right)} \operatorname{prerequisiteMeet}\left(edge, label, predecessor\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/DependencyAggregateRecursion.prerequisiteMeet_recursion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Dually, the global prerequisite meet equals the node label met with every direct predecessor's prerequisite meet.

The complete-lattice assumption is an instance binder. No distributivity or finite-lattice hypothesis is added.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/DependencyAggregateRecursion.prerequisiteJoin_recursion`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/DependencyAggregateRecursion.prerequisiteMeet_recursion`
- Dependency: [D5/S3/ConceptDynamics/DagSemantics/DependencyAggregate](../DagSemantics/DependencyAggregate.md)
