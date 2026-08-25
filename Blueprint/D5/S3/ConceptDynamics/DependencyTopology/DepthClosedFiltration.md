# Depth-Closed Filtration

## Abstract

Strict edge depth yields a closed Alexandrov sublevel filtration.

**Theorem 1.1 (Strict reachability strictly increases compatible depth).**

$$\forall edge: V \to V \to \operatorname{Prop}, depth: V \to \mathbb{N}, u, v: V, (\operatorname{DepthCompatible}\left(edge, depth\right) \land \operatorname{StrictReachable}\left(edge, u, v\right)) \Rightarrow depth(u) < depth(v).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DependencyTopology/DepthClosedFiltration.depth_strict_of_strictReachable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Depth compatibility requires every edge to move from a smaller natural depth to a larger one.

Induction along a nonempty reachability path composes these strict inequalities, so the path endpoint has strictly larger depth.

**Theorem 1.2 (Every compatible depth sublevel is closed).**

$$\forall edge: V \to V \to \operatorname{Prop}, depth: V \to \mathbb{N}, n: \mathbb{N}, \operatorname{DepthCompatible}\left(edge, depth\right) \Rightarrow \operatorname{IsClosed}\left(\operatorname{upperSetTopology}\left(\operatorname{Reachable}\left(edge\right)\right), \operatorname{depthSublevel}\left(depth, n\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DependencyTopology/DepthClosedFiltration.depthSublevel_isClosed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reachability can only increase a depth compatible with the edge relation. Therefore the strict superlevel above any natural level is upward closed.

Upward-closed sets are open in the dependency Alexandrov topology. The complementary sublevel is consequently closed.

The conclusion is conditional on DepthCompatible and is asserted for the explicitly displayed level only.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/DepthClosedFiltration.depthSublevel_isClosed`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/DepthClosedFiltration.depth_strict_of_strictReachable`
- Dependency: [D5/S3/ConceptDynamics/DependencyTopology/AlexandrovDependencyTopology](AlexandrovDependencyTopology.md)
