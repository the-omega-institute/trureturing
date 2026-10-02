# FishburnTenTenAMonotone

## Abstract

Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.

**Theorem 1.1 (Monotone permutations and maximum insertion).**

Lean statement: `D5/S3/Combinatorics/Fishburn/FishburnTenTenAMonotone.a_monotone_forms`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Fishburn/FishburnTenTenAMonotone.a_monotone_forms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

For every nonnegative n, both the increasing and decreasing permutations of one through n are Fishburn permutations avoiding 2143, 1423 and 3124. Among positions zero through n, inserting n plus one into the increasing permutation preserves these conditions exactly at zero or at a position s with n at most s plus one. For the decreasing permutation the permitted positions are exactly zero and n.

## References

- Truth anchor: `D5/S3/Combinatorics/Fishburn/FishburnTenTenAMonotone.a_monotone_forms`
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnBasic2143](FishburnBasic2143.md)
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnBasicPatterns](FishburnBasicPatterns.md)
