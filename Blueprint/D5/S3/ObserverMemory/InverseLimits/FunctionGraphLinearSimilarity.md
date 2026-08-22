# Linear Similarity of the Colliding Function Graphs

## Abstract

The two eight-state transition matrices are linearly similar over the integers.

**Theorem 1.1 (An integral unit intertwines the two transition matrices).**

$$\exists P: \operatorname{Matrix}(Fin(8), Fin(8), \mathbb{Z}),\ \operatorname{IsUnit}(P) \land transitionMatrix(tauA) * P = P * transitionMatrix(tauB).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/InverseLimits/FunctionGraphLinearSimilarity.transition_matrices_linearly_similar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a self-map f of Fin 8, transitionMatrix(f) uses the column convention: its (i,j)-entry is one exactly when f(j)=i. The definition imports and applies the frozen tauA and tauB tables; it does not copy either table into a second source.

The certificate is the displayed integral matrix similarityWitness. A second explicit integral matrix is checked on both sides as its inverse, so similarityWitness is a unit in the matrix ring. Exact finite arithmetic then verifies transitionMatrix(tauA) P = P transitionMatrix(tauB).

This theorem certifies the positive half of proposition 8.5 for the specific pair: the transition matrices lie in the same linear similarity class. The frozen collision theorem certifies the negative half: their spectra collide, but no permutation conjugates the underlying based function graphs. These separately certified declarations are the atom's two formal halves.

Repository, pinned-Mathlib, and GitHub Lean-code searches found no equal or stronger declaration. The proof therefore uses the explicit finite certificate and Mathlib's standard matrix-unit interface.

## References

- Truth anchor: `D5/S3/ObserverMemory/InverseLimits/FunctionGraphLinearSimilarity.transition_matrices_linearly_similar`
- Dependency: [D5/S3/ObserverMemory/InverseLimits/FunctionGraphSpectrumCollision](FunctionGraphSpectrumCollision.md)
