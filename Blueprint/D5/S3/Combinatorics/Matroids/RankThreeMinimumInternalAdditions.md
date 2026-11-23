# The Least Internal Additions for an Extra Ternary Dimension

## Abstract

Fix the mixed lifted-line triples of a ternary row space with cyclic row size three times r.

**Theorem 1.1 (The extra dimension forces a minimum number of additions).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeMinimumInternalAdditions.internal_additions_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeMinimumInternalAdditions.internal_additions_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the internal residue test permits the extra dimension, the total number of rows in basis coordinates is multiplied by three and each resulting fiber has size r. Apply the mixed-pair lower bound to the enlarged triple family. Subtracting the exact number of original mixed triples leaves at least r squared internal triples per original row.

**Theorem 1.2 (Transversals on the residue fibers meet the bound).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeMinimumInternalAdditions.exists_internal_additions_attaining`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeMinimumInternalAdditions.exists_internal_additions_attaining` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Index each of the three residue classes by a cyclic coordinate of size r. In each row, choose one point from each class using two free cyclic coordinates and their negative sum. Every different-residue pair in a row then occurs exactly once. Both internal residue tests hold, while the original mixed triples are retained. There are exactly r squared additions per row. The indexing uses the residue fibers as sets and applies also when the cyclic row size is divisible by nine.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeMinimumInternalAdditions.exists_internal_additions_attaining`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeMinimumInternalAdditions.internal_additions_lower_bound`
- Dependency: [D5/S3/Combinatorics/Matroids/RankThreeInternalTriplePotentials](RankThreeInternalTriplePotentials.md)
- Dependency: [D5/S3/Combinatorics/Matroids/RankThreeOmissionPairCount](RankThreeOmissionPairCount.md)
