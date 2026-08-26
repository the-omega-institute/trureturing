# Reachability Projection Invariance

## Abstract

Prerequisite and consequence closures depend only on reachability, not the chosen direct-edge presentation.

**Theorem 1.1 (Reachability-equivalent graphs have equal prerequisite closures).**

$$\forall firstEdge, secondEdge: V \to V \to Prop, targets: \operatorname{Set}\left(V\right),\\{}\operatorname{SameReachability}\left(firstEdge, secondEdge\right) \Rightarrow\\{}\operatorname{prerequisiteClosure}\left(firstEdge, targets\right) = \operatorname{prerequisiteClosure}\left(secondEdge, targets\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/ReachabilityProjectionInvariance.prerequisiteClosure_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two direct-edge relations induce the same reflexive-transitive reachability relation, they generate identical prerequisite closures of every displayed target set.

The SameReachability hypothesis is explicit; equality of direct edge relations is neither assumed nor concluded.

**Theorem 1.2 (Reachability-equivalent graphs have equal consequence closures).**

$$\forall firstEdge, secondEdge: V \to V \to Prop, sources: \operatorname{Set}\left(V\right),\\{}\operatorname{SameReachability}\left(firstEdge, secondEdge\right) \Rightarrow\\{}\operatorname{consequenceClosure}\left(firstEdge, sources\right) = \operatorname{consequenceClosure}\left(secondEdge, sources\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/ReachabilityProjectionInvariance.consequenceClosure_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same pair of reachability-equivalent presentations, consequence closures of a displayed source set are equal.

The theorem changes only the edge presentation and holds the source set fixed on both sides.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/ReachabilityProjectionInvariance.consequenceClosure_eq`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/ReachabilityProjectionInvariance.prerequisiteClosure_eq`
- Dependency: [D5/S3/ConceptDynamics/DagCompletion/ConsequenceClosure](ConsequenceClosure.md)
- Dependency: [D5/S3/ConceptDynamics/DependencyTopology/DependencyReachabilityOrder](../DependencyTopology/DependencyReachabilityOrder.md)
