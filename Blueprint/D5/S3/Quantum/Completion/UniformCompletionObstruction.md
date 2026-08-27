# Uniform Completion Obstruction

## Abstract

Proper Hilbert-subspace projections remain one operator-norm unit from the identity.

**Theorem 1.1 (Proper projection stages stay uniformly separated from identity).**

$$\begin{gathered}\forall K, H, I: Type,\\{}[\operatorname{RCLike}\left(K\right)], [\operatorname{NormedAddCommGroup}\left(H\right)],\\{}[\operatorname{InnerProductSpace}\left(K, H\right)],\\{}S: I \to \operatorname{Submodule}_{K}(H),\\{}[\forall i: I, \operatorname{HasOrthogonalProjection}\left(S(i)\right)],\\{}stageFilter: \operatorname{Filter}\left(I\right), [\operatorname{NeBot}\left(stageFilter\right)],\\hProper: {\forall i: I, S(i) \neq top},\\((\forall i: I, \left\lVert \operatorname{id}\left(K, H\right) - \operatorname{starProjection}\left(S(i)\right) \right\rVert = 1) \land\\\neg \operatorname{Tendsto}\left({\Lambda i: I, \left\lVert \operatorname{id}\left(K, H\right) - \operatorname{starProjection}\left(S(i)\right) \right\rVert}, stageFilter, \operatorname{nhds}\left(0\right)\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/UniformCompletionObstruction.uniform_completion_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a family of proper closed subspaces of a Hilbert space, indexed along a nontrivial stage filter, and let each stage map be its canonical orthogonal projection.

Identity minus the stage projection is the orthogonal projection onto the nonzero complementary subspace. Its operator norm is exactly one at every stage.

Consequently the operator-norm distances cannot converge to zero along the stage filter.

## References

- Truth anchor: `D5/S3/Quantum/Completion/UniformCompletionObstruction.uniform_completion_obstruction`
- Dependency: [D5/S3/Quantum/Completion/InfiniteDimensionalProjectionSeparation](InfiniteDimensionalProjectionSeparation.md)
