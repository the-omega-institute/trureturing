# Finite Observability Orthogonal Duality

## Abstract

Each finite readout kernel is the orthogonal complement of its observable Krylov space.

**Theorem 1.1 (Finite hidden and observable spaces are orthogonal duals).**

$$\forall K, V, Y, T, C, m,\\{}\operatorname{RCLike}(K) \land \operatorname{NormedAddCommGroup}(V) \land \operatorname{InnerProductSpace}(K, V) \land \operatorname{FiniteDimensional}(K, V) \land\\{}\operatorname{NormedAddCommGroup}(Y) \land \operatorname{InnerProductSpace}(K, Y) \land \operatorname{FiniteDimensional}(K, Y) \land\\{}T \in \operatorname{LinearMap}(K, V, V) \land C \in \operatorname{LinearMap}(K, V, Y) \land m \in N \Rightarrow\\{}N_{m} := \operatorname{iInf}(0 \le k \le m, \operatorname{ker}(C \circ T^{k})); O_{m} := \operatorname{span}(K, \{{T^{*}}^{k}(C^{*}(y)) \mid 0 \le k \le m, y \in Y\});\\{}N_{m} = O_{m}^{\perp}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Dynamics/FiniteObservabilityOrthogonalDuality.finite_unobservable_eq_observable_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V and Y be finite-dimensional inner-product spaces over a real or complex scalar field. Let T evolve V linearly, let C read V linearly into Y, and fix a nonnegative depth m.

The finite hidden space intersects the kernels of C composed with T to the kth power for every k at most m. The finite observable space uses the family's canonical observableKrylov construction: the span of the matching adjoint-orbit vectors.

The sole public conclusion identifies the hidden space with the orthogonal complement of that independently constructed visible space. It applies uniformly at every finite depth.

Repository and pinned-library searches found no packaged finite-depth duality theorem. The proof directly applies the adjoint inner-product identity and span induction in both directions.

## References

- Truth anchor: `D5/S3/ObserverMemory/Dynamics/FiniteObservabilityOrthogonalDuality.finite_unobservable_eq_observable_orthogonal`
- Dependency: [D5/S3/ObserverMemory/Dynamics/InfiniteObservabilityOrthogonalDuality](InfiniteObservabilityOrthogonalDuality.md)
