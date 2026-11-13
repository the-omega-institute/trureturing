# MarkeyFiveSiteGrowthDifference

## Abstract

Markey five-site growth differs from the Shannon vertex count by 4*n+7.

**Definition 1.1 (MarkeyA400701.claim).**

$$\operatorname{MarkeyA400701}.\operatorname{claim} \iff (\forall (a b : (\operatorname{EuclideanSpace} \mathbb{R} (\operatorname{Fin} 2))) , a \neq b \to \forall (n : \mathbb{N}) , 1 < n \to \operatorname{MarkeyA400701}.\operatorname{latticeCount} n = \operatorname{ShannonA374338}.\operatorname{vertexCount} a b n + 4 \cdot n + 7)$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/MarkeyFiveSiteGrowthDifference.claim` (`✓ std3`).

*Citation.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

OEIS A400701 revision 30, NAME (unpaginated), verbatim: “Start with a set of five adjacent collinear points in a hexagonal lattice. Every iteration, add to the set the points in the lattice which are adjacent to at least two points already in the set. This sequence gives the number of points in the set after n iterations.” FORMULA, verbatim: “Conjectured: For n > 1: a(n) = A374338(n) + 4*n + 7.” The lattice has six unit directions. Both counts use the same natural iteration index.

**Theorem 1.2 (MarkeyA400701.result).**

$$\forall (a b : (\operatorname{EuclideanSpace} \mathbb{R} (\operatorname{Fin} 2))) , a \neq b \to \forall (n : \mathbb{N}) , 1 < n \to \operatorname{MarkeyA400701}.\operatorname{latticeCount} n = \operatorname{ShannonA374338}.\operatorname{vertexCount} a b n + 4 \cdot n + 7$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Percolation/MarkeyFiveSiteGrowthDifference.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

The five-site count exceeds the two-site circle count by 4*n+7 at every iteration n>1.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/MarkeyFiveSiteGrowthDifference.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/MarkeyFiveSiteGrowthDifference.result`
- Dependency: [D5/S3/Geometry/ShannonFixedRadiusCircleVertices](../../Geometry/ShannonFixedRadiusCircleVertices.md)
- Dependency: [D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap](DirectProductCyclePathBootstrap.md)
- Dependency: [D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth](TriangularTwoNeighborGrowth.md)
