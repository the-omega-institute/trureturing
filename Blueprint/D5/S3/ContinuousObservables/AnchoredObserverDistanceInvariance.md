# Anchored Observer Distance Invariance

## Abstract

Compatible group actions preserve observer distance and anchored radius.

**Theorem 1.1 (Compatible actions preserve the observer geometry).**

$$\forall G \in Type, A \in Type, X \in Type, O \in \operatorname{Set}\left(A\right), L \in A \to [0, \infty], e \in X \to \left(A \to \mathbb{R}\right), o \in X,\; \left(\left(\operatorname{Group}\left(G\right) \land \left(\operatorname{MulAction}\left(G, A\right) \land \operatorname{MulAction}\left(G, X\right)\right)\right) \land \left(\left(\forall g \in G, f \in A,\; f \in O \Rightarrow \operatorname{act}\left(g, f\right) \in O\right) \land \left(\left(\forall g \in G, f \in A,\; f \in O \Rightarrow L\left(\operatorname{act}\left(g, f\right)\right) = L\left(f\right)\right) \land \left(\forall g \in G, f \in A, x \in X,\; e\left(\operatorname{act}\left(g, x\right), \operatorname{act}\left(g, f\right)\right) = e\left(x, f\right)\right)\right)\right)\right) \Rightarrow \left(\operatorname{observerDistance}\left(O, L, e, o, o\right) = 0 \land \left(\left(\forall g \in G, x \in X, y \in X,\; \operatorname{observerDistance}\left(O, L, e, \operatorname{act}\left(g, x\right), \operatorname{act}\left(g, y\right)\right) = \operatorname{observerDistance}\left(O, L, e, x, y\right)\right) \land \left(\forall g \in G, x \in X,\; \operatorname{act}\left(g, o\right) = o \Rightarrow \operatorname{observerDistance}\left(O, L, e, o, \operatorname{act}\left(g, x\right)\right) = \operatorname{observerDistance}\left(O, L, e, o, x\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/AnchoredObserverDistanceInvariance.anchored_observer_distance_invariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The action transports every admissible observable, preserves its cost, and commutes with evaluation. Reindexing the unit-cost supremum by the inverse action proves distance invariance in both directions.

## References

- Truth anchor: `D5/S3/ContinuousObservables/AnchoredObserverDistanceInvariance.anchored_observer_distance_invariance`
- Dependency: [D5/S3/Observer/Separation/RefinementDistanceMonotonicity](../Observer/Separation/RefinementDistanceMonotonicity.md)
