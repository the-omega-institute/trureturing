# Maximal Unobservable Subspace

## Abstract

The all-future readout kernel is the maximal invariant hidden subspace.

**Theorem 1.1 (The future kernel is maximal among invariant hidden subspaces).**

$$\forall K, V, Y: \operatorname{Type}, [\operatorname{RCLike}\left(K\right)], [\operatorname{NormedAddCommGroup}\left(V\right)], [\operatorname{InnerProductSpace}\left(K, V\right)], [\operatorname{FiniteDimensional}\left(K, V\right)], [\operatorname{NormedAddCommGroup}\left(Y\right)], [\operatorname{InnerProductSpace}\left(K, Y\right)], [\operatorname{FiniteDimensional}\left(K, Y\right)]\\{}T: \operatorname{LinearMap}\left(K, V, V\right), C: \operatorname{LinearMap}\left(K, V, Y\right),\\{}N_{\infty} := \operatorname{iInf}\left(k, \operatorname{ker}\left(C \circ T^{k}\right)\right);\\{}N_{\infty} \subseteq \operatorname{ker}\left(C\right) \land \operatorname{MapsTo}\left(T, N_{\infty}, N_{\infty}\right) \land\\{}\forall M: \operatorname{Submodule}\left(K, V\right), (M \subseteq \operatorname{ker}\left(C\right) \land \operatorname{MapsTo}\left(T, M, M\right)) \Rightarrow M \subseteq N_{\infty}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Dynamics/MaximalUnobservableSubspace.future_kernel_is_maximal_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V and Y be finite-dimensional inner-product spaces over a real or complex scalar field. Let T evolve V linearly and let C read V linearly into Y.

The hidden subspace is constructed canonically as the intersection of the kernels of C composed with every power of T. This is the source all-future readout test, not a definition by maximality.

The public theorem states all maximality clauses: the future kernel lies inside ker(C), T maps it into itself, and every T-invariant subspace inside ker(C) is contained in it.

The zero iterate proves current invisibility, shifting an iterate proves invariance, and induction keeps every iterate of a point in any competing invariant subspace.

## References

- Truth anchor: `D5/S3/ObserverMemory/Dynamics/MaximalUnobservableSubspace.future_kernel_is_maximal_invariant`
- Dependency: [D5/S3/ObserverMemory/Dynamics/ObservableKrylovGrowthBound](ObservableKrylovGrowthBound.md)
