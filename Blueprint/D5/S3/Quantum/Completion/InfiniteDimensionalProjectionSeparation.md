# Infinite-Dimensional Projection Separation

## Abstract

Dense finite-dimensional Hilbert projection towers converge on every vector while remaining a unit operator-norm distance from the identity.

**Theorem 1.1 (Dense finite projection towers complete pointwise but not uniformly).**

$$\begin{gathered}\forall K, H, \operatorname{Hilbert}\left(K, H\right), \operatorname{InfiniteDimensional}\left(K, H\right),\\S: \mathbb{N} \to \operatorname{ClosedSubspace}\left(H\right), \operatorname{Monotone}\left(S\right),\\(\forall n, \operatorname{FiniteDimensional}\left(K, S(n)\right)), \operatorname{Cumulative}\left(S\right) = H,\\(\forall n, S(n) \neq H) \land\\(\forall x\in H, \operatorname{lim}\left(n, \infty, \operatorname{P}\left(S(n)\right)(x)\right) = x) \land\\\neg (\operatorname{lim}\left(n, \infty, \left\lVert I - \operatorname{P}\left(S(n)\right) \right\rVert\right) = 0) \land\\(\forall n, \left\lVert I - \operatorname{P}\left(S(n)\right) \right\rVert = 1).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/InfiniteDimensionalProjectionSeparation.infinite_dimensional_projection_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be an increasing sequence of finite-dimensional closed subspaces of an infinite-dimensional Hilbert space, with cumulative closed span equal to the whole ambient space.

No finite stage equals the ambient space. The canonical orthogonal projections nevertheless converge to the identity on every fixed vector, by the increasing-projection strong-limit theorem.

At every stage, the identity-minus-projection operator is the orthogonal projection onto the nonzero complementary subspace. Its operator norm is therefore exactly one, so the norm sequence cannot converge to zero.

## References

- Truth anchor: `D5/S3/Quantum/Completion/InfiniteDimensionalProjectionSeparation.infinite_dimensional_projection_separation`
- Dependency: [D5/S3/Quantum/Completion/IncreasingProjectionStrongLimit](IncreasingProjectionStrongLimit.md)
