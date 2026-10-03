# Active Positions for 2413 and 2431 Avoiders

## Abstract

Interval suffixes and separating cuts characterize active positions for Fishburn permutations avoiding 2413 and 2431.

**Theorem 1.1 (The interval-suffix criterion).**

Lean statement: `D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenSites.interval_active_sites`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenSites.interval_active_sites` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Let p be a Fishburn permutation of length n avoiding 2413 and 2431 and let s be a position from zero through its length. Inserting n + 1 at s preserves these conditions exactly when the values in the suffix beginning at s form an order-connected set of natural numbers and, whenever an entry immediately before s exists, it is not one greater than any entry at or after s. Order-connected means that every natural number between two suffix values is also a suffix value.

**Theorem 1.2 (Updating the interval positions).**

Lean statement: `D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenSites.interval_site_updates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenSites.interval_site_updates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Let p be a Fishburn permutation of positive length n avoiding 2413 and 2431, and suppose insertion of n + 1 at position s preserves those conditions. For every gap g at most s, insertion of n + 2 at g in the resulting permutation is permitted exactly when every entry of p before g is less than every entry at or after g. Insertion immediately after n + 1 is permitted exactly when the original maximum n occurs before s in p. For every gap g strictly after s and at most the length of p, insertion of n + 2 at g + 1 in the resulting permutation is permitted exactly when insertion of n + 1 at g in p is permitted. Positions are numbered from zero.

## References

- Truth anchor: `D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenSites.interval_active_sites`
- Truth anchor: `D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenSites.interval_site_updates`
- Dependency: [D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicTenThirteenPatterns](FishburnBasicTenThirteenPatterns.md)
