# Observer Horizon Refinement

## Abstract

Refinement can only enlarge the infinite-distance observer horizon.

**Theorem 1.1 (The observer horizon grows under refinement).**

$$\forall A \in Type, X \in Type, e \in X \to \left(A \to \mathbb{R}\right), o \in X, Am \in \operatorname{Set}\left(A\right), Am1 \in \operatorname{Set}\left(A\right), Lm \in A \to [0, \infty], Lm1 \in A \to [0, \infty],\; \left(Am \subseteq Am1 \land \left(\forall f \in A,\; f \in Am \Rightarrow Lm1\left(f\right) = Lm\left(f\right)\right)\right) \Rightarrow \left\{\operatorname{observerDistance}\left(Am, Lm, e, o, x\right) = \infty \mid x \in X\right\} \subseteq \left\{\operatorname{observerDistance}\left(Am1, Lm1, e, o, x\right) = \infty \mid x \in X\right\}$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/ObserverHorizonRefinement.observer_horizon_mono_of_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every old unit-cost observable remains available after refinement. The frozen distance monotonicity theorem therefore sends an old top-valued distance to a top-valued refined distance.

## References

- Truth anchor: `D5/S3/ContinuousObservables/ObserverHorizonRefinement.observer_horizon_mono_of_refinement`
- Dependency: [D5/S3/Observer/Separation/RefinementDistanceMonotonicity](../Observer/Separation/RefinementDistanceMonotonicity.md)
