# Axiom Closure Monotonicity

## Abstract

Edge-local monotone labels remain monotone along dependency reachability.

**Theorem 1.1 (Local label monotonicity extends to every reachable pair).**

$$\begin{gathered}\forall edge: V \to V \to \operatorname{Prop},\\{}label: V \to \operatorname{Set}\left(Atom\right), u, v: V,\\{}((\forall a, b: V, edge(a, b) \Rightarrow label(a) \subseteq label(b)) \land \operatorname{Reachable}\left(edge, u, v\right)) \Rightarrow\\{}label(u) \subseteq label(v).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DependencyTopology/AxiomClosureMonotonicity.label_mono_of_edge_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let every dependency edge carry the source label into the target label by set inclusion.

A reflexive-transitive reachability path is built from zero or more such edge steps. Induction on that path composes the inclusions.

Consequently, every atom attached at a reachable source is still present at the reachable target. No converse inclusion is claimed.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/AxiomClosureMonotonicity.label_mono_of_edge_mono`
- Dependency: [D5/S3/ConceptDynamics/DependencyTopology/DependencyReachabilityOrder](DependencyReachabilityOrder.md)
