# Path connected weight profiles with an admissible choice

## Abstract

Strictly positive normalized profiles with a singleton weight form a path-connected set when there are at least three labels.

**Theorem 1.1 (Positive normalized profiles with a singleton weight are path connected).**

$$\forall I:\operatorname{Type}, [\operatorname{Fintype}\left(I\right)], 2 < \operatorname{card}\left(I\right) \Rightarrow \operatorname{IsPathConnected}\left(\{w:I \to \mathbb{R} \mid (\forall i:I, 0 < \operatorname{w}\left(i\right)) \land \operatorname{sum}\left(w\right) = 1 \land (\exists i:I, \forall j:I, \operatorname{w}\left(j\right) = \operatorname{w}\left(i\right) \Rightarrow j = i)\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/FiniteSimplexSelection.pathConnected_normalized_profiles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite label type I of cardinality at least three, consider all real profiles with strictly positive weights, sum one, and a weight occurring at exactly one label. The set of such profiles is path connected.

If every weight occurs more than once, each label admits a distinct peer of the same weight. A fixed-point-free map sending labels to such peers specifies a linear subspace by requiring all its peer equalities. The profiles without a singleton weight are the union of these finitely many subspaces. Each remains proper after adjoining any line. To see this, take a label i and a label k outside the pair formed by i and its peer. If the added vector agrees on the first pair, the coordinate spike at i is excluded. If it disagrees, any decomposition of the spike at k would force the coefficient of the added vector to vanish, which contradicts the peer equality at k.

The positive cone outside these subspaces is path connected. Dividing each vector by the sum of its weights is continuous there and preserves equality of coordinates. Its image is the stated subset of the probability simplex.

A continuous rule on this domain with discrete outcome labels would be constant by connectedness. A permutation moving the chosen label conflicts with equivariance. The assertion about continuous selection is a consequence of path connectedness and the permutation invariance of the domain.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/FiniteSimplexSelection.pathConnected_normalized_profiles`
- Dependency: [D5/S3/Topology/FiniteSubspaceComplement](../../Topology/FiniteSubspaceComplement.md)
