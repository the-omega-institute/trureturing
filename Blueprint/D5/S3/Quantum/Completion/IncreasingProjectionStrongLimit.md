# Increasing Projection Strong Limit

## Abstract

Increasing orthogonal projections converge strongly to the cumulative projection and, under terminal completeness, to the identity.

**Theorem 1.1 (Increasing projections have the cumulative strong limit).**

$$\begin{gathered}\forall K, H, \operatorname{Hilbert}\left(K, H\right),\\S: \mathbb{N} \to \operatorname{ClosedSubspace}\left(H\right), \operatorname{Monotone}\left(S\right),\\Sinf = \overline{\operatorname{iSup}\left(n, S(n)\right)}, Rinf = Sinf^{\perp},\\(\forall x\in H, \operatorname{lim}\left(n, \infty, \operatorname{P}\left(S(n)\right)(x)\right) = \operatorname{P}\left(Sinf\right)(x)) \land\\(Rinf = 0 \Rightarrow \operatorname{SOTlim}\left(n, \infty, \operatorname{P}\left(S(n)\right)\right) = I).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/IncreasingProjectionStrongLimit.increasing_projection_strong_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be an increasing sequence of closed projection subspaces of a Hilbert space. Its cumulative space is the closure of the supremum of the finite stages, and its terminal residual is the orthogonal complement of that cumulative space.

For every vector x, the orthogonal projections onto S(n) converge in norm to the orthogonal projection onto the cumulative space. This is the vectorwise form of the increasing-projection limit.

When the terminal residual is zero, the cumulative space is the whole Hilbert space. The same vectorwise limits then assemble through Mathlib's pointwise-convergence topology on continuous linear maps, the strong operator topology, into convergence to the identity.

## References

- Truth anchor: `D5/S3/Quantum/Completion/IncreasingProjectionStrongLimit.increasing_projection_strong_limit`
- Dependency: [D5/S3/Quantum/Completion/BoundedInverseLimitReconstruction](BoundedInverseLimitReconstruction.md)
