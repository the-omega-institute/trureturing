# Limit Residual Decomposition

## Abstract

The intersection of stage residuals is the cumulative orthogonal complement.

**Theorem 1.1 (The limit residual is the cumulative orthogonal complement).**

$$\begin{gathered}\forall K, H, \operatorname{CompleteHilbertSpace}\left(K, H\right),\\{}S: \mathbb{N} \to \operatorname{Subspace}\left(K, H\right),\\{}\operatorname{limitingResidual}\left(S\right) = \operatorname{cumulativeSpace}\left(S\right)^{\perp} \land\\{}\operatorname{IsCompl}\left(\operatorname{cumulativeSpace}\left(S\right), \operatorname{limitingResidual}\left(S\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/LimitResidualDecomposition.limit_residual_orthogonal_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a sequence of subspaces in a complete real-or-complex inner-product space. Its cumulative space is the closure of the supremum of the stages.

The limiting residual is constructed independently as the intersection of the orthogonal complements of all stages. It equals the orthogonal complement of the cumulative space.

The equality identifies the two canonical constructions, and the second conjunct states that the cumulative space and limiting residual form an internal direct sum of the ambient Hilbert space.

## References

- Truth anchor: `D5/S3/Quantum/Completion/LimitResidualDecomposition.limit_residual_orthogonal_decomposition`
- Dependency: [D5/S3/Quantum/Completion/BoundedInverseLimitReconstruction](BoundedInverseLimitReconstruction.md)
