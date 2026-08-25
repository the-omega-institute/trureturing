# Dependency Reachability Order

## Abstract

Acyclic dependency reachability is a partial order.

**Theorem 1.1 (Acyclic reachability has the three partial-order laws).**

$$\begin{gathered}\forall edge: V \to V \to \operatorname{Prop},\\{}\operatorname{AcyclicEdge}\left(edge\right) \Rightarrow\\{}(\operatorname{Reflexive}\left(\operatorname{Reachable}\left(edge\right)\right) \land \operatorname{Transitive}\left(\operatorname{Reachable}\left(edge\right)\right) \land\\{}(\forall u, v: V, (\operatorname{Reachable}\left(edge, u, v\right) \land \operatorname{Reachable}\left(edge, v, u\right)) \Rightarrow u = v)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DependencyTopology/DependencyReachabilityOrder.reachable_partial_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reachable is the reflexive-transitive closure of the supplied edge relation, while StrictReachable requires at least one edge.

Reflexivity and transitivity follow from the closure construction. Acyclicity rules out strict paths that return to their source.

If two vertices reach one another and are distinct, their two strict paths compose to a forbidden cycle. Thus mutual reachability forces equality.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/DependencyReachabilityOrder.reachable_partial_order`
