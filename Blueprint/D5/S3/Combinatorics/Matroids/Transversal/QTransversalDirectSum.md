# Direct sums of transversal q-matroids

## Abstract

The concatenated presentation computes the rank of the direct sum.

**Definition 1.1 (Coordinate splitting).**

Lean statement: `D5/S3/Combinatorics/Matroids/Transversal/QTransversalDirectSum.splitCoordinates`

*Formalization.* `D5/S3/Combinatorics/Matroids/Transversal/QTransversalDirectSum.splitCoordinates` (`✓ std3`).

*Citation.* Andrew Fulcher (2026). *A cyclic flat embedding theorem for transversal q-matroids*. DOI: [10.48550/arXiv.2603.13550](https://doi.org/10.48550/arXiv.2603.13550). URL: <https://arxiv.org/abs/2603.13550v1>.

*Commentary.*

Split a vector indexed by Fin (m + n) into its first m and last n coordinates. This linear equivalence identifies the combined coordinate space with the product of the two factor spaces.

**Definition 1.2 (First projection).**

Lean statement: `D5/S3/Combinatorics/Matroids/Transversal/QTransversalDirectSum.firstProjection`

*Formalization.* `D5/S3/Combinatorics/Matroids/Transversal/QTransversalDirectSum.firstProjection` (`✓ std3`).

*Citation.* Andrew Fulcher (2026). *A cyclic flat embedding theorem for transversal q-matroids*. DOI: [10.48550/arXiv.2603.13550](https://doi.org/10.48550/arXiv.2603.13550). URL: <https://arxiv.org/abs/2603.13550v1>.

*Commentary.*

Take the first factor after splitting the coordinates.

**Definition 1.3 (Second projection).**

Lean statement: `D5/S3/Combinatorics/Matroids/Transversal/QTransversalDirectSum.secondProjection`

*Formalization.* `D5/S3/Combinatorics/Matroids/Transversal/QTransversalDirectSum.secondProjection` (`✓ std3`).

*Citation.* Andrew Fulcher (2026). *A cyclic flat embedding theorem for transversal q-matroids*. DOI: [10.48550/arXiv.2603.13550](https://doi.org/10.48550/arXiv.2603.13550). URL: <https://arxiv.org/abs/2603.13550v1>.

*Commentary.*

Take the second factor after splitting the coordinates.

**Definition 1.4 (Concatenated presentation).**

Lean statement: `D5/S3/Combinatorics/Matroids/Transversal/QTransversalDirectSum.concatenatedPresentation`

*Formalization.* `D5/S3/Combinatorics/Matroids/Transversal/QTransversalDirectSum.concatenatedPresentation` (`✓ std3`).

*Citation.* Andrew Fulcher (2026). *A cyclic flat embedding theorem for transversal q-matroids*. DOI: [10.48550/arXiv.2603.13550](https://doi.org/10.48550/arXiv.2603.13550). URL: <https://arxiv.org/abs/2603.13550v1>.

*Commentary.*

Pull back every slot of the first family along the first projection, then every slot of the second family along the second projection. Under the coordinate equivalence the slots are the products of a first-family slot with the entire second space and the entire first space with a second-family slot.

**Theorem 1.5 (Fulcher Conjecture 4.8).**

$$\forall (F: Type), [Field\left(F\right)] [Fintype\left(F\right)] \forall (m: \mathbb{N}), \forall (n: \mathbb{N}), \forall (k: \mathbb{N}), \forall (l: \mathbb{N}), \forall (X: Fin\left(k\right) \to Submodule\left(F, Fin\left(m\right) \to F\right)), \forall (Y: Fin\left(l\right) \to Submodule\left(F, Fin\left(n\right) \to F\right)), \forall (U: Submodule\left(F, Fin\left(m + n\right) \to F\right)), qTransversalRank\left(concatenatedPresentation\left(X, Y\right), U\right) = sInf\left(\{d \mid \exists (W: Submodule\left(F, Fin\left(m + n\right) \to F\right)), W \le U \land d = qTransversalRank\left(X, \operatorname{Submodule}.\operatorname{map}\left(firstProjection, W\right)\right) + qTransversalRank\left(Y, \operatorname{Submodule}.\operatorname{map}\left(secondProjection, W\right)\right) + (\operatorname{Module}.\operatorname{finrank}\left(F, U\right) - \operatorname{Module}.\operatorname{finrank}\left(F, W\right))\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/Transversal/QTransversalDirectSum.fulcher_conjecture_4_8` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrew Fulcher (2026). *A cyclic flat embedding theorem for transversal q-matroids*. DOI: [10.48550/arXiv.2603.13550](https://doi.org/10.48550/arXiv.2603.13550). URL: <https://arxiv.org/abs/2603.13550v1>.

*Commentary.*

The rank uses the original definition by dimensions of every-basis partial q-transversals. Each finite indexed family permits repetitions and can be empty. Both factor terms in the minimum use the same subspace W contained in U. The admissible costs are natural numbers and the set of costs contains the value at W = U, so its infimum is attained.

The one-presentation Hall formula expresses rank as the minimum of the number of slots failing to contain a test subspace plus its codimension. For a common W, take a minimizing subspace in each projected space. Their joint preimage in W projects into both minimizers, with codimension at most the sum of the projected codimensions. In the other direction, use a minimizer for the concatenated presentation as W and bound each factor rank by the slot count at its full projected space.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/Transversal/QTransversalDirectSum.concatenatedPresentation`
- Truth anchor: `D5/S3/Combinatorics/Matroids/Transversal/QTransversalDirectSum.firstProjection`
- Truth anchor: `D5/S3/Combinatorics/Matroids/Transversal/QTransversalDirectSum.fulcher_conjecture_4_8`
- Truth anchor: `D5/S3/Combinatorics/Matroids/Transversal/QTransversalDirectSum.secondProjection`
- Truth anchor: `D5/S3/Combinatorics/Matroids/Transversal/QTransversalDirectSum.splitCoordinates`
- Dependency: [D5/S3/Combinatorics/Matroids/QTransversalRepresentability](../QTransversalRepresentability.md)
