# Observable Krylov Growth Bound

## Abstract

Strict growth of the finite observable Krylov tower is bounded by missing rank.

**Theorem 1.1 (Strict observable-tower growth is rank bounded).**

$$\forall K, V, Y, T, C,\ \operatorname{encard}\left(\{m \in N \mid \operatorname{observableKrylov}\left(T, C, m\right) < \operatorname{observableKrylov}\left(T, C, m + 1\right)\}\right) \le \operatorname{finrank}\left(K, V\right) - \operatorname{finrank}\left(K, \operatorname{range}\left(C\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Dynamics/ObservableKrylovGrowthBound.observable_krylov_strict_growth_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V and Y be finite-dimensional inner-product spaces over a real or complex scalar field, let T evolve V linearly, and let C read V linearly into Y. The m-th observable Krylov space is constructed as the span of (T*)^k(C*y) for k at most m.

The set of indices where this canonical tower grows strictly has cardinality at most dim(V) minus rank(C). This is the theorem's sole public clause; the dimension increase and initial-rank identity are its proof, not independent conjuncts.

Every strict inclusion raises finrank, so sending a growth index to the current finrank injects it into the natural interval from rank(C) to dim(V). The zero-stage space is range(C*), whose finrank equals rank(C).

Required-family and pinned-Mathlib searches found no packaged Krylov growth-count theorem. The proof directly applies Mathlib's strict-submodule finrank inequality, adjoint-range rank identity, injective set-cardinality bound, and natural-interval count.

## References

- Truth anchor: `D5/S3/ObserverMemory/Dynamics/ObservableKrylovGrowthBound.observable_krylov_strict_growth_bound`
