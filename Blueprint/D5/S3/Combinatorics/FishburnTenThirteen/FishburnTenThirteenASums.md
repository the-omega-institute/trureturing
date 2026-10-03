# Active Positions in Direct Sums Avoiding 2413 and 2431

## Abstract

Active positions in a direct sum avoiding 2413 and 2431 combine component boundaries on the left with active positions on the right.

**Theorem 1.1 (Separating cuts and right-component positions).**

Lean statement: `D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenASums.interval_sum_sites`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenASums.interval_sum_sites` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Let u be a permutation of length m, let v be a nonempty Fishburn permutation of length n avoiding 2413 and 2431, and suppose their direct sum is also Fishburn and avoids both patterns. A position s from zero through m in the left component permits insertion of m + n + 1 exactly when every entry of u before s is less than every entry after s. A position s from zero through n in v permits that insertion at m + s in the direct sum exactly when insertion of n + 1 at s in v preserves the same conditions. If v is sum-indecomposable, every positive active position in v has the maximum n before it. If u is assembled from a list of nonempty sum-indecomposable permutation components, the number of active positions in the direct sum equals the number of those components plus the number of active positions in v.

## References

- Truth anchor: `D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenASums.interval_sum_sites`
- Dependency: [D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicComponentCuts](FishburnBasicComponentCuts.md)
- Dependency: [D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicSum](FishburnBasicSum.md)
- Dependency: [D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenSites](FishburnTenThirteenSites.md)
