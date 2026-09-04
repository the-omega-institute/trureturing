# Canonical Strongest Separating Observer

## Abstract

The normalized orthogonal residual is the canonical strongest separating observer.

**Theorem 1.1 (Optimal residual readout and its exact maximizers).**

$$\forall H \in \operatorname{RealHilbertSpace}\left(\right), M \in \operatorname{ClosedSubspace}\left(H\right), x \in H,\; \operatorname{proj}\left(\operatorname{orthogonalComplement}\left(M\right), x\right) \neq 0 \Rightarrow \left(\operatorname{sup}_{g: g\in \operatorname{orthogonalComplement}\left(M\right) \land \left\lVert g \right\rVert \leq 1} {\Vert\operatorname{inner}\left(g, x\right)\Vert} = \left\lVert \operatorname{proj}\left(\operatorname{orthogonalComplement}\left(M\right), x\right) \right\rVert \land \left(\left(\forall g \in H,\; \left(g\in \operatorname{orthogonalComplement}\left(M\right) \land \left\lVert g \right\rVert \leq 1\right) \Rightarrow \left(\Vert\operatorname{inner}\left(g, x\right)\Vert = \left\lVert \operatorname{proj}\left(\operatorname{orthogonalComplement}\left(M\right), x\right) \right\rVert \Leftrightarrow \left(g = \operatorname{proj}\left(\operatorname{orthogonalComplement}\left(M\right), x\right) / \left\lVert \operatorname{proj}\left(\operatorname{orthogonalComplement}\left(M\right), x\right) \right\rVert \lor g = -\operatorname{proj}\left(\operatorname{orthogonalComplement}\left(M\right), x\right) / \left\lVert \operatorname{proj}\left(\operatorname{orthogonalComplement}\left(M\right), x\right) \right\rVert\right)\right)\right) \land \left(\forall g \in H,\; \left(\left(g\in \operatorname{orthogonalComplement}\left(M\right) \land \left\lVert g \right\rVert \leq 1\right) \land \operatorname{inner}\left(g, x\right) = \left\lVert \operatorname{proj}\left(\operatorname{orthogonalComplement}\left(M\right), x\right) \right\rVert\right) \Rightarrow g = \operatorname{proj}\left(\operatorname{orthogonalComplement}\left(M\right), x\right) / \left\lVert \operatorname{proj}\left(\operatorname{orthogonalComplement}\left(M\right), x\right) \right\rVert\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CanonicalStrongestSeparatingObserver.canonical_strongest_separating_observer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M be a closed subspace of a real Hilbert space, let x be a target, and let r be the orthogonal projection of x onto the orthogonal complement of M. Assume r is nonzero.

The supremum of the absolute readout over observers in the orthogonal unit ball is the norm of r, and both signs of the normalized residual attain it.

These are the only absolute-value maximizers. After requiring positive alignment, the normalized residual is the unique maximizer. This corrects the source's false uniqueness claim for an absolute objective.

## References

- Truth anchor: `D5/S3/Observer/CanonicalStrongestSeparatingObserver.canonical_strongest_separating_observer`
