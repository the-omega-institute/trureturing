# FishburnTenSevenUnimodal

## Abstract

Avoiding 213 and 312 forces a list of distinct entries to increase and then decrease around its maximum.

**Theorem 1.1 (Unimodality and two-pattern avoidance).**

Lean statement: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenUnimodal.unimodal_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenUnimodal.unimodal_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Let a list with no repeated entry consist of a left block, a peak, and a right block, with every entry of the two blocks below the peak. The list avoids both 213 and 312 if and only if the left block is strictly increasing and the right block is strictly decreasing.

## References

- Truth anchor: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenUnimodal.unimodal_iff`
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnBasicAscents](../Fishburn/FishburnBasicAscents.md)
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnDefs](../Fishburn/FishburnDefs.md)
