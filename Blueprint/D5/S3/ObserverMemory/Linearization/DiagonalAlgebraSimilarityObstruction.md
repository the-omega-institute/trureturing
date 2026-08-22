# Diagonal-Algebra Similarity Obstruction

## Abstract

Similar transition matrices need not admit a diagonal-algebra-preserving similarity.

**Theorem 1.1 (Similar transition matrices can differ as based systems).**

$$\begin{gathered}(\exists P, Q: \operatorname{Matrix}\left(\operatorname{Fin}\left(8\right), \operatorname{Fin}\left(8\right), \mathbb{C}\right),\\{}PQ = I \land QP = I \land\\{}\operatorname{complexTransitionMatrix}\left(tauA\right)P = P\operatorname{complexTransitionMatrix}\left(tauB\right)) \land\\{}\neg(\exists P, Q: \operatorname{Matrix}\left(\operatorname{Fin}\left(8\right), \operatorname{Fin}\left(8\right), \mathbb{C}\right),\\{}PQ = I \land QP = I \land\\{}\operatorname{complexTransitionMatrix}\left(tauA\right)P = P\operatorname{complexTransitionMatrix}\left(tauB\right) \land\\{}(\forall d: \operatorname{Fin}\left(8\right) \to \mathbb{C}, \exists d': \operatorname{Fin}\left(8\right) \to \mathbb{C}, P\operatorname{diag}\left(d\right)Q = \operatorname{diag}\left(d'\right)) \land\\{}(\forall d: \operatorname{Fin}\left(8\right) \to \mathbb{C}, \exists d': \operatorname{Fin}\left(8\right) \to \mathbb{C}, Q\operatorname{diag}\left(d\right)P = \operatorname{diag}\left(d'\right))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Linearization/DiagonalAlgebraSimilarityObstruction.same_linear_class_without_diagonal_algebra_similarity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The maps tauA and tauB are imported from the canonical eight-state countermodel. Their complex transition matrices use the standard basis: column y is the coordinate vector indexed by tau(y).

The first public conjunct gives an explicit complex change of basis and two-sided inverse intertwining the transition matrices. This is the source's common complex linear similarity class, and hence its common Jordan form.

The second public conjunct rules out any such change of basis that also conjugates every standard diagonal matrix to a diagonal matrix in both directions. Thus the quantified property is directly about the full diagonal algebra, not a definition by graph conjugacy.

The proof applies the frozen integral similarity certificate after entrywise complex casting. Conversely, conjugated coordinate diagonals force each matrix column onto a distinct coordinate row, producing a permutation conjugacy forbidden by the frozen function-graph countermodel.

## References

- Truth anchor: `D5/S3/ObserverMemory/Linearization/DiagonalAlgebraSimilarityObstruction.same_linear_class_without_diagonal_algebra_similarity`
- Dependency: [D5/S3/ObserverMemory/InverseLimits/FunctionGraphLinearSimilarity](../InverseLimits/FunctionGraphLinearSimilarity.md)
