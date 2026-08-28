# Infinite Observability Orthogonal Duality

## Abstract

The all-future readout kernel is the orthogonal complement of the observable orbit.

**Theorem 1.1 (The infinite hidden and observable spaces are orthogonal duals).**

$$\forall K, V, Y, T, C,\\{}\operatorname{RCLike}(K) \land \operatorname{NormedAddCommGroup}(V) \land \operatorname{InnerProductSpace}(K, V) \land \operatorname{FiniteDimensional}(K, V) \land\\{}\operatorname{NormedAddCommGroup}(Y) \land \operatorname{InnerProductSpace}(K, Y) \land \operatorname{FiniteDimensional}(K, Y) \land\\{}T \in \operatorname{LinearMap}(K, V, V) \land C \in \operatorname{LinearMap}(K, V, Y) \Rightarrow\\{}N_{\infty} := \operatorname{iInf}(k, \operatorname{ker}(C \circ T^{k})); O_{\infty} := \operatorname{span}(K, \{{T^{*}}^{k}(C^{*}(y)) \mid k \in N, y \in Y\});\\{}N_{\infty} = O_{\infty}^{\perp}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Dynamics/InfiniteObservabilityOrthogonalDuality.infinite_unobservable_eq_observable_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V and Y be finite-dimensional inner-product spaces over a real or complex scalar field. Let T evolve V linearly and let C read V linearly into Y.

The hidden space is constructed from the kernels of C composed with every nonnegative power of T. Independently, the observable space is the span of every vector obtained by applying an adjoint power of T to a vector in the adjoint image of C.

The public equality states that the all-future hidden space is exactly the orthogonal complement of that observable span. Each side is therefore determined by the source dynamics and readout before the equality is proved.

Repository and pinned-library searches found no packaged theorem with this full statement. The proof applies the library's adjoint inner-product identity and span induction in both directions.

## References

- Truth anchor: `D5/S3/ObserverMemory/Dynamics/InfiniteObservabilityOrthogonalDuality.infinite_unobservable_eq_observable_orthogonal`
- Dependency: [D5/S3/ObserverMemory/Dynamics/ObservableKrylovGrowthBound](ObservableKrylovGrowthBound.md)
