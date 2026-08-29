# Finite Acyclic Judging Graph Root

## Abstract

A finite nonempty acyclic judging graph has a vertex with no incoming judge.

**Theorem 1.1 (A finite acyclic judging graph has a root).**

$$\begin{gathered}\forall V: \operatorname{Type}, [\operatorname{Finite}(V)], [\operatorname{Nonempty}(V)],\\{}judges: V \to V \to Prop,\\{}\operatorname{AcyclicEdge}\left(judges\right) \Rightarrow \exists r: V, \forall j: V, \neg judges(j, r).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Governance/FiniteAcyclicJudgingGraphRoot.finite_acyclic_judging_graph_has_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

AcyclicEdge excludes a nonempty directed cycle in the judging relation. On a finite carrier, the transitive closure is therefore well-founded, and so is the original judging relation.

The existing well-founded-frontier theorem applied to the full vertex set yields a ready vertex. Readiness against the complement of the full set says exactly that no vertex judges it.

The result asserts only existence of an empty-judge vertex. It does not assert that this vertex certifies its own consistency.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Governance/FiniteAcyclicJudgingGraphRoot.finite_acyclic_judging_graph_has_root`
- Dependency: [D5/S3/ConceptDynamics/DagCompletion/WellFoundedFrontier](../DagCompletion/WellFoundedFrontier.md)
- Dependency: [D5/S3/ConceptDynamics/DependencyTopology/DependencyReachabilityOrder](../DependencyTopology/DependencyReachabilityOrder.md)
