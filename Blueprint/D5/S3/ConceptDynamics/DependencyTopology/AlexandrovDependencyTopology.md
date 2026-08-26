# Alexandrov Dependency Topology

## Abstract

Upper sets form the dependency Alexandrov topology with principal opens and downset closures.

**Theorem 1.1 (A singleton closes to its principal downset).**

$$\forall R: V \to V \to \operatorname{Prop}, x: V, (\operatorname{Refl}\left(R\right) \land \operatorname{IsTrans}\left(V, R\right)) \Rightarrow \operatorname{closure}\left(\operatorname{upperSetTopology}\left(R\right), \operatorname{singleton}\left(x\right)\right) = \operatorname{downset}\left(R, x\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DependencyTopology/AlexandrovDependencyTopology.closure_singleton_eq_downset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a reflexive and transitive relation and equip its carrier with the topology whose open sets are upward closed.

The closure of a point consists exactly of the vertices that reach that point under the relation. This is the principal downset.

The proof identifies specialization with the reverse relation and then applies the standard specialization characterization of singleton closure.

**Theorem 1.2 (Principal downsets grow along the relation).**

$$\forall R: V \to V \to \operatorname{Prop}, x, y: V, (\operatorname{Refl}\left(R\right) \land \operatorname{IsTrans}\left(V, R\right) \land R(x, y)) \Rightarrow \operatorname{downset}\left(R, x\right) \subseteq \operatorname{downset}\left(R, y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DependencyTopology/AlexandrovDependencyTopology.downset_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For related vertices x and y, every predecessor of x is also a predecessor of y.

Transitivity supplies the required composite relation step, so the principal downset at x is contained in the one at y.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/AlexandrovDependencyTopology.closure_singleton_eq_downset`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/AlexandrovDependencyTopology.downset_mono`
- Dependency: [D5/S3/ConceptDynamics/DependencyTopology/DependencyReachabilityOrder](DependencyReachabilityOrder.md)
