# Target Observability Four-Way Equivalence

## Abstract

A linear target is observable exactly when its Riesz vector lies in the adjoint range.

**Theorem 1.1 (Four equivalent criteria for linear target observability).**

$$\begin{gathered}\forall K, X, Y: Type,\\{}\operatorname{RCLike}(K) \land \operatorname{NormedAddCommGroup}(X) \land \operatorname{InnerProductSpace}(K, X) \land \operatorname{FiniteDimensional}(K, X) \land\\{}\operatorname{NormedAddCommGroup}(Y) \land \operatorname{InnerProductSpace}(K, Y) \land \operatorname{FiniteDimensional}(K, Y) \Rightarrow\\{}\forall M: \operatorname{LinearMap}(K, X, Y), t: \operatorname{LinearMap}(K, X, K), v_{t}: X,\\{}(\forall x: X, t(x) = \operatorname{inner}(v_{t}, x)) \Rightarrow\\{}((\forall x, y: X, M(x) = M(y) \Rightarrow t(x) = t(y)) \iff \operatorname{ker}(M) \subseteq \operatorname{ker}(t)) \land\\{}((\forall x, y: X, M(x) = M(y) \Rightarrow t(x) = t(y)) \iff v_{t} \in \operatorname{range}(\operatorname{adjoint}(M))) \land\\{}((\forall x, y: X, M(x) = M(y) \Rightarrow t(x) = t(y)) \iff \exists a: Y, \operatorname{adjoint}(M)(a) = v_{t}) \land\\{}(\forall a: Y, \operatorname{adjoint}(M)(a) = v_{t} \Rightarrow \forall x: X, t(x) = \operatorname{inner}(a, M(x))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/VisibleDescent/TargetObservabilityFourWayEquivalence.target_observability_four_way_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The target functional is represented on the source Hilbert space by its displayed Riesz vector. Constancy on observation fibers is equivalent to inclusion of the observation kernel in the target kernel.

Finite-dimensional orthogonal duality identifies that condition with membership of the Riesz vector in the adjoint range. Every displayed adjoint preimage reconstructs the target from the observation.

## References

- Truth anchor: `D5/S3/Observer/VisibleDescent/TargetObservabilityFourWayEquivalence.target_observability_four_way_equivalence`
