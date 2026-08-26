# Strong Component Quotient

## Abstract

Quotienting a directed relation by mutual reachability yields a partial order of strong components.

**Theorem 1.1 (Component reachability is antisymmetric).**

$$\forall edge: V \to V \to Prop, first, second: \operatorname{StrongComponent}\left(edge\right),\\{}(\operatorname{componentReachable}\left(edge, first, second\right) \land \operatorname{componentReachable}\left(edge, second, first\right)) \Rightarrow first = second.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/StrongComponentQuotient.componentReachable_antisymm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take two strong components. If each component reaches the other under the quotient reachability relation, the components are equal.

Mutual reachability was already used to form each quotient class; this theorem supplies the antisymmetry needed by the partial-order instance.

**Theorem 1.2 (Strict component reachability has no cycle).**

$$\forall edge: V \to V \to Prop, component: \operatorname{StrongComponent}\left(edge\right),\\{}\neg \operatorname{TransGen}\left(\operatorname{strictComponentReachability}\left(edge\right), component, component\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/StrongComponentQuotient.no_strict_component_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any strong component, there is no nonempty cycle made of steps that reach forward without reaching backward.

The displayed strict-component relation abbreviates forward component reachability together with failure of reverse reachability.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/StrongComponentQuotient.componentReachable_antisymm`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/StrongComponentQuotient.no_strict_component_cycle`
- Dependency: [D5/S3/ConceptDynamics/DagSemantics/PrerequisiteClosure](../DagSemantics/PrerequisiteClosure.md)
- Dependency: [D5/S3/ConceptDynamics/DependencyTopology/DependencyReachabilityOrder](../DependencyTopology/DependencyReachabilityOrder.md)
