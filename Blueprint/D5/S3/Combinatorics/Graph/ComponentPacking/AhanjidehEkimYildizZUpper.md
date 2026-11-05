# AhanjidehEkimYildizZUpper

## Abstract

Finite graph structure, degree counting, and perfect matchings.

**Theorem 1.1 (attainment).**

$$\forall (large: \operatorname{Bool}), \forall (k: \mathbb{N}), ((5 \leq k))\to((let d = 4 \cdot k + (if large then 3 else 1); \exists (N: \mathbb{N}), \exists (G: \operatorname{SimpleGraph} (\operatorname{Fin} N)), (\operatorname{IsAlmostRegular} G d)\land((G . \operatorname{CliqueFree} 3)\land((\operatorname{IsFactorCritical} G)\land(\operatorname{matchingNumber} G = \operatorname{Nat} . \operatorname{div} (5 \cdot (d + 1)) 4)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZUpper.attainment` (`✓ std3`). ∎

*Citation.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

Proposition 4.3, page 8, gives the upper-bound graphs. The two thirteen-bag constructions give almost regular, triangle-free, factor-critical graphs for degrees 4k + 1 and 4k + 3. Their orders are twice the stated matching number plus one. Natural division denotes floor division.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZUpper.attainment`
- Dependency: [D5/S3/Combinatorics/Graph/ComponentPacking/FactorCriticalMatching](FactorCriticalMatching.md)
- Dependency: [D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction](PentagonMissingEdgeObstruction.md)
- Dependency: [D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation](../../../StatisticalMechanics/DimerVirialFourthDifferenceRefutation.md)
