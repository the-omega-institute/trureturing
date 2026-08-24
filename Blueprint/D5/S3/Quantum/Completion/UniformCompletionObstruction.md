# Uniform Completion Obstruction

## Abstract

Proper Hilbert-subspace projections remain one operator-norm unit from the identity.

**Theorem 1.1 (Proper projection stages stay uniformly separated from identity).**

$$\begin{gathered}\forall K, H, A, L,\\\operatorname{Hilbert}\left(K, H\right), \operatorname{NeBot}\left(L\right), S: A \to \operatorname{ClosedSubspace}\left(H\right),\\(\forall a, S(a) \neq H) \implies \\((\forall a, \left\lVert I - \operatorname{P}\left(S(a)\right) \right\rVert = 1) \land\\\neg (\operatorname{lim}\left(a, L, \left\lVert I - \operatorname{P}\left(S(a)\right) \right\rVert\right) = 0)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/UniformCompletionObstruction.uniform_completion_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a family of proper closed subspaces of a Hilbert space, indexed along a nontrivial stage filter, and let each stage map be its canonical orthogonal projection.

Identity minus the stage projection is the orthogonal projection onto the nonzero complementary subspace. Its operator norm is exactly one at every stage.

Consequently the operator-norm distances cannot converge to zero along the stage filter.

## References

- Truth anchor: `D5/S3/Quantum/Completion/UniformCompletionObstruction.uniform_completion_obstruction`
- Dependency: [D5/S3/Quantum/Completion/InfiniteDimensionalProjectionSeparation](InfiniteDimensionalProjectionSeparation.md)
