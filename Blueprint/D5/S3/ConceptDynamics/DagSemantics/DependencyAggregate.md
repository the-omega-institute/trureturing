# Dependency Aggregate

## Abstract

Meet and join aggregates over prerequisite cones are antitone and monotone along dependency reachability.

**Theorem 1.1 (Prerequisite meets decrease downstream).**

$$\forall edge: V \to V \to Prop, label: V \to Label,\\{}first, second: V, [\operatorname{CompleteLattice}\left(Label\right)],\\{}\operatorname{ReflTransGen}\left(edge, first, second\right) \Rightarrow\\{}\operatorname{prerequisiteMeet}\left(edge, label, second\right) \leq \operatorname{prerequisiteMeet}\left(edge, label, first\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/DependencyAggregate.prerequisiteMeet_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a complete lattice, a path from the first node to the second enlarges the second node's prerequisite cone. Meeting over that larger cone can only decrease the aggregate.

The displayed path is the sole propositional hypothesis. The complete lattice remains an instance binder, not an added conjunct.

**Theorem 1.2 (Prerequisite joins increase downstream).**

$$\forall edge: V \to V \to Prop, label: V \to Label,\\{}first, second: V, [\operatorname{CompleteLattice}\left(Label\right)],\\{}\operatorname{ReflTransGen}\left(edge, first, second\right) \Rightarrow\\{}\operatorname{prerequisiteJoin}\left(edge, label, first\right) \leq \operatorname{prerequisiteJoin}\left(edge, label, second\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/DependencyAggregate.prerequisiteJoin_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same reachable pair, every label contributing to the upstream join also contributes to the downstream join.

Therefore the first join is below the second. No strict inequality or finiteness of the prerequisite cone is claimed.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagSemantics/DependencyAggregate.prerequisiteJoin_mono`
- Truth anchor: `D5/S3/ConceptDynamics/DagSemantics/DependencyAggregate.prerequisiteMeet_antitone`
