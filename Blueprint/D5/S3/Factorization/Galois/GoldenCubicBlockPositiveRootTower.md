# Positive-Root Lucas-Block Tower

## Abstract

The positive real Lucas-block cube roots generate a degree-three tower over the concrete cubic cyclotomic field in the complex numbers.

**Theorem 1.1 (The concrete positive-root tower has degree three to the number of blocks).**

$$\begin{aligned}\omega := \operatorname{exp}\left(\frac{2 \pi i}{3}\right), K := \mathbb{Q}(\omega) \subset \mathbb{C},\\B_{j} := \left(L_{3^{j}}\right)^{2}+3, \beta_{j} := \left(B_{j}\right)^{\frac{1}{3}} \in \mathbb{R}_{>0} \subset \mathbb{C},\\K_{J} := \operatorname{adjoin}\left(K, \{\beta_{j} \mid j \in \mathbb{N}, 1 \le j \le J\}\right),\\\forall J \in \mathbb{N}, [K_{J}:K] = 3^{J}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/GoldenCubicBlockPositiveRootTower.golden_cubic_block_positive_root_tower_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here omega is exp(2 pi i / 3), and K is the concrete subfield Q(omega) of C. Each B_j is the positive integer L_(3^j)^2 + 3. The element beta_j is its positive real cube root, embedded in C; K_J adjoins precisely those beta_j with indices from one through J.

The proof transports the degree from the abstract third cyclotomic field to this complex copy. In a field containing the cubic roots of unity, any two cube roots of the same nonzero block generate the same subfield. This identifies each positive-root stage with the corresponding abstract stage, whose degree is three.

For positive J this is the Lucas-block tower of the stated theory. The Lean conclusion also includes J equal to zero, where the tower is K and has degree one. No field discriminant, ramification law, or Galois-group structure is asserted.

## References

- Truth anchor: `D5/S3/Factorization/Galois/GoldenCubicBlockPositiveRootTower.golden_cubic_block_positive_root_tower_degree`
- Dependency: [D5/S3/Factorization/Galois/GoldenCubicBlockKummerTower](GoldenCubicBlockKummerTower.md)
