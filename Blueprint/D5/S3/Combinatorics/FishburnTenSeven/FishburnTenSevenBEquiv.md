# FishburnTenSevenBEquiv

## Abstract

An interval construction produces permutations in the second triple-avoidance class.

**Theorem 1.1 (Membership of the second interval form).**

Lean statement: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBEquiv.B_typeII_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBEquiv.B_typeII_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Let two be at most d, d at most h, h less than m, and m at most n. For any Fishburn permutation q of length d minus two avoiding 213, concatenate the decreasing interval from n through m plus one, the decreasing interval from h through d, one, the increasing interval from h plus one through m minus one, m, and q with every entry increased by one. The resulting list is a Fishburn permutation of length n avoiding 1324, 2143 and 3124.

## References

- Truth anchor: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBEquiv.B_typeII_mem`
- Dependency: [D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBParameters](FishburnTenSevenBParameters.md)
- Dependency: [D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBStructure](FishburnTenSevenBStructure.md)
