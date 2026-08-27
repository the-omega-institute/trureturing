# Consequence Closure

## Abstract

Reachability generates the least successor-closed consequence set, dual to prerequisite closure.

**Theorem 1.1 (Consequence closure is the least successor-closed superset).**

$$\forall edge: V \to V \to Prop, sources, closed: \operatorname{Set}\left(V\right),\\{}(sources \subseteq closed \land \operatorname{SuccessorClosed}\left(edge, closed\right)) \Rightarrow\\{}\operatorname{consequenceClosure}\left(edge, sources\right) \subseteq closed.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/ConsequenceClosure.consequenceClosure_least` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a set contains all sources and is closed under direct dependents, it contains every node reachable from a source.

The two closure hypotheses are explicit antecedents, and the conclusion is exactly containment of the generated consequence closure.

**Theorem 1.2 (Prerequisite membership is witnessed by a consequence intersection).**

$$\forall edge: V \to V \to Prop, targets: \operatorname{Set}\left(V\right), node: V,\\{}node \in \operatorname{prerequisiteClosure}\left(edge, targets\right) \iff\\{}\operatorname{Nonempty}\left(\operatorname{inter}\left(\operatorname{consequenceClosure}\left(edge, \operatorname{singleton}\left(node\right)\right), targets\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/ConsequenceClosure.mem_prerequisiteClosure_iff_consequence_inter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A node is in the prerequisite closure of a target set exactly when its singleton consequence cone meets that target set.

The equivalence uses the same reachability direction on both sides and does not assert equality of the two closure sets.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/ConsequenceClosure.consequenceClosure_least`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/ConsequenceClosure.mem_prerequisiteClosure_iff_consequence_inter`
- Dependency: [D5/S3/ConceptDynamics/DagSemantics/PrerequisiteClosure](../DagSemantics/PrerequisiteClosure.md)
- Dependency: [D5/S3/ConceptDynamics/DependencyTopology/DependencyReachabilityOrder](../DependencyTopology/DependencyReachabilityOrder.md)
