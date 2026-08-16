# The Markov Neighbor Norm Obstruction

## Abstract

The neighboring Markov factors cannot multiply to a norm of the form x^2 + 3y^2.

**Theorem 1.1 (The neighboring factors do not form a quadratic norm).**

$$\forall mu, x, y \in \mathbb{Z},\ x^{2}+3y^{2} \neq (3mu-1)(3mu+1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/MarkovNeighborNormObstruction.markov_neighbor_product_not_quadratic_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all integers mu, x, and y, the product (3mu - 1)(3mu + 1) cannot equal x^2 + 3y^2. The product is 9mu^2 - 1, hence has the form 3m - 1 with m = 3mu^2.

The proof applies the existing repository theorem ModThreeNormObstruction.three_mul_sub_one_not_quadratic_norm directly after the factor identity. Pinned Mathlib source search and two skill searches found no exact theorem. Online Loogle returned zero declarations for both the integer norm obstruction and its square-modulo-three core.

This node closes only the even-branch arithmetic sentence in appendix E.52: the displayed neighboring-factor product is excluded by the modulo-three norm obstruction. It does not formalize the full Markov-geodesic avoidance theorem, the crossing-spectrum lower bound, or either numerical census.

## References

- Truth anchor: `D5/S3/Arith/Congruence/MarkovNeighborNormObstruction.markov_neighbor_product_not_quadratic_norm`
- Dependency: [D5/S3/Arith/Congruence/ModThreeNormObstruction](ModThreeNormObstruction.md)
