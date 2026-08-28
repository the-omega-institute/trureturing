# Alexandrov Monotone Continuity

## Abstract

Maps between upper Alexandrov spaces are continuous exactly when they are monotone.

**Theorem 1.1 (Continuity between upper Alexandrov spaces is monotonicity).**

$$\begin{gathered}\forall relationX: X \to X \to \operatorname{Prop}, relationY: Y \to Y \to \operatorname{Prop}, map: X \to Y,\\{}[\operatorname{Refl}\left(relationX\right)] [\operatorname{IsTrans}\left(X, relationX\right)] [\operatorname{Refl}\left(relationY\right)] [\operatorname{IsTrans}\left(Y, relationY\right)] \Rightarrow\\{}(\operatorname{Continuous}\left(\operatorname{upperSetTopology}\left(relationX\right), \operatorname{upperSetTopology}\left(relationY\right), map\right) \iff \operatorname{RelationMonotone}\left(relationX, relationY, map\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DependencyTopology/AlexandrovMonotoneContinuity.continuous_upperSetTopology_iff_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix reflexive and transitive relations on the source and target and give each carrier its upper-set Alexandrov topology.

Continuity pulls the principal upset of a mapped source point back to an open source set. Upward closure of that preimage forces the map to preserve the relation.

Conversely, a relation-preserving map sends every source relation step to a target relation step, so preimages of target upper sets are upper and therefore open.

**Theorem 1.2 (A monotone dependency map is continuous).**

$$\forall edgeX: X \to X \to \operatorname{Prop}, edgeY: Y \to Y \to \operatorname{Prop}, map: X \to Y,\\{}\operatorname{RelationMonotone}\left(\operatorname{Reachable}\left(edgeX\right), \operatorname{Reachable}\left(edgeY\right), map\right) \Rightarrow\\{}\operatorname{Continuous}\left(\operatorname{dependencyTopology}\left(edgeX\right), \operatorname{dependencyTopology}\left(edgeY\right), map\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DependencyTopology/AlexandrovMonotoneContinuity.monotone_continuous_dependencyTopology` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RelationMonotone here means that the map preserves reflexive-transitive dependency reachability from the source graph to the target graph.

Applying the upper-Alexandrov equivalence to those two reachability relations yields continuity between the corresponding dependency topologies.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/AlexandrovMonotoneContinuity.continuous_upperSetTopology_iff_monotone`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/AlexandrovMonotoneContinuity.monotone_continuous_dependencyTopology`
- Dependency: [D5/S3/ConceptDynamics/DependencyTopology/AlexandrovDependencyTopology](AlexandrovDependencyTopology.md)
