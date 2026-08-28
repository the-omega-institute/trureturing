# Alexandrov Inseparability

## Abstract

Upper-Alexandrov inseparability is mutual reachability and antisymmetry.

**Theorem 1.1 (Upper-Alexandrov inseparability is mutual relatedness).**

$$\forall relation: V \to V \to \operatorname{Prop}, x, y: V,\\{}[\operatorname{Refl}\left(relation\right)] [\operatorname{IsTrans}\left(V, relation\right)] \Rightarrow\\{}(\operatorname{Inseparable}\left(\operatorname{upperSetTopology}\left(relation\right), x, y\right) \iff relation(x, y) \land relation(y, x)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DependencyTopology/AlexandrovInseparability.upper_inseparable_iff_mutual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equip a carrier with the topology of sets that are upward closed for a reflexive and transitive relation.

The principal upset of either point is open. Inseparability forces each point into the other's principal upset, giving both relation directions.

Conversely, mutual relatedness transports membership through every upper-open set in both directions, so no open set separates the points.

**Theorem 1.2 (Antisymmetry is equality of inseparable points).**

$$\forall relation: V \to V \to \operatorname{Prop},\\{}[\operatorname{Refl}\left(relation\right)] [\operatorname{IsTrans}\left(V, relation\right)] \Rightarrow\\{}((\forall x, y: V, (relation(x, y) \land relation(y, x)) \Rightarrow x = y) \iff (\forall x, y: V, \operatorname{Inseparable}\left(\operatorname{upperSetTopology}\left(relation\right), x, y\right) \Rightarrow x = y)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DependencyTopology/AlexandrovInseparability.antisymmetric_iff_inseparable_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the displayed reflexivity and transitivity instances, the preceding characterization identifies inseparability with two opposing relation steps.

The relation is antisymmetric exactly when every such mutually related, and hence inseparable, pair is equal.

**Theorem 1.3 (Acyclic dependency topology separates distinct points).**

$$\forall edge: V \to V \to \operatorname{Prop}, x, y: V,\\{}(\operatorname{AcyclicEdge}\left(edge\right) \land \operatorname{Inseparable}\left(\operatorname{dependencyTopology}\left(edge\right), x, y\right)) \Rightarrow x = y.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DependencyTopology/AlexandrovInseparability.dependency_inseparable_implies_eq_of_acyclic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Dependency reachability is reflexive and transitive. Acyclicity makes it antisymmetric because opposing nontrivial paths would compose to a cycle.

Therefore two points inseparable in the dependency Alexandrov topology must coincide.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/AlexandrovInseparability.antisymmetric_iff_inseparable_eq`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/AlexandrovInseparability.dependency_inseparable_implies_eq_of_acyclic`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/AlexandrovInseparability.upper_inseparable_iff_mutual`
- Dependency: [D5/S3/ConceptDynamics/DependencyTopology/AlexandrovDependencyTopology](AlexandrovDependencyTopology.md)
