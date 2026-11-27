# Excluding five direction types in a cubic Laurent component

## Abstract

Five opposite-parity direction triples are impossible.

**Theorem 1.1 (Five opposite-parity direction triples are impossible).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentFiveTypeExclusion.card_directionTypes_ne_five`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentFiveTypeExclusion.card_directionTypes_ne_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Five types would give two partitions sharing a block. Projection away from that block gives four slices with threefold fibers and a common integer height. The box rigidity theorem excludes coexistence of both complementary splits. This removes a case of the one-sided Laurent approach to Hong, Wu and Xia’s Problem 2.

**Theorem 1.2 (Fifty-four vertices or at least seven direction triples).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentFiveTypeExclusion.card_eq_fiftyFour_or_seven_le_directionTypes`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentFiveTypeExclusion.card_eq_fiftyFour_or_seven_le_directionTypes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With at most three triples, the neighbor partition is constant. The projected boxes have one split and one center, so the projection has nine points. Its threefold fibers give twenty-seven vertices on the selected side. Cubic regularity gives the same number on the opposite side. The direction count gap and the five-type exclusion leave at least seven types at every other order.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentFiveTypeExclusion.card_directionTypes_ne_five`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentFiveTypeExclusion.card_eq_fiftyFour_or_seven_le_directionTypes`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentCommonTriple](Q9LaurentCommonTriple.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentDirectionTypes](Q9LaurentDirectionTypes.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentNormalizedBoxes](Q9LaurentNormalizedBoxes.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentStarProducts](Q9LaurentStarProducts.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentTransverseFibers](Q9LaurentTransverseFibers.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ProjectedHeightCompatibility](../Q9ProjectedHeightCompatibility.md)
