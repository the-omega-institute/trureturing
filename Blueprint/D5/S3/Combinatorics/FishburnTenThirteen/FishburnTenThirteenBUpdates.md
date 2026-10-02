# Updating Active Positions for 2431 and 3241 Avoiders

## Abstract

Two successive maximum insertions in the 2431 and 3241 avoidance class are controlled by inequalities across the insertion positions.

**Theorem 1.1 (Active positions after one insertion).**

Lean statement: `D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBUpdates.crossing_site_updates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBUpdates.crossing_site_updates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Let p be a Fishburn permutation of positive length n avoiding 2431 and 3241, and suppose insertion of n + 1 at position s preserves those conditions. For every gap g at most s, insertion of n + 2 at g in the resulting permutation is permitted exactly when g is active in p and every entry of p before g is less than every entry at or after s. For every gap g strictly after s and at most the length of p, insertion of n + 2 at g + 1 is permitted exactly when g is active in p and every entry from s through g - 1 is less than every entry at or after g. Insertion immediately after n + 1 is permitted exactly when the original maximum n occurs before s in p. If s is zero and p is assembled from a list of nonempty sum-indecomposable permutation components, the resulting permutation has as many active positions as there are components plus one. Positions are numbered from zero.

## References

- Truth anchor: `D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBUpdates.crossing_site_updates`
- Dependency: [D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicComponentCuts](FishburnBasicComponentCuts.md)
- Dependency: [D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicTenThirteenPatterns](FishburnBasicTenThirteenPatterns.md)
