# Active Positions in Direct Sums Avoiding 2431 and 3241

## Abstract

Maximum-insertion positions in a direct sum avoiding 2431 and 3241 are determined componentwise.

**Theorem 1.1 (Componentwise insertion and crossing inequalities).**

Lean statement: `D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBSums.crossing_sum_sites`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBSums.crossing_sum_sites` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Let u and v be Fishburn permutations of lengths m and n avoiding 2431 and 3241, and suppose their direct sum avoids the same patterns and is Fishburn. For every position s from zero through m, insertion of m + n + 1 at s in the direct sum preserves these conditions exactly when insertion of m + 1 at s in u does so. For every position s from zero through n, insertion at m + s in the direct sum is permitted exactly when insertion of n + 1 at s in v is permitted. Moreover, if the entry at a position h in the direct sum is m + n and a permitted insertion position s is strictly after h, every entry strictly between h and s is less than every entry at or after s. Positions are numbered from zero.

## References

- Truth anchor: `D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBSums.crossing_sum_sites`
- Dependency: [D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicTenThirteenPatterns](FishburnBasicTenThirteenPatterns.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum](../Nonnesting/NonnestingBasicSum.md)
