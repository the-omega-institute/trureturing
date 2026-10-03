# FishburnTenSevenBStructure

## Abstract

Permutations in the second triple-avoidance class have one of two interval forms.

**Theorem 1.1 (Interval forms for the second class).**

Lean statement: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBStructure.B_interval_normalForm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBStructure.B_interval_normalForm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

For positive n, every Fishburn permutation of length n avoiding 1324, 2143 and 3124 has an m between one and n and one of two forms. The first is the decreasing interval from n through m plus one followed by a Fishburn permutation of length m avoiding 213 and starting with one. The second has two at most d, d at most h, and h less than m, and consists of the decreasing interval from n through m plus one, the decreasing interval from h through d, one, the increasing interval from h plus one through m minus one, m, and a Fishburn permutation of length d minus two avoiding 213 with each entry increased by one.

## References

- Truth anchor: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBStructure.B_interval_normalForm`
- Dependency: [D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenAuxiliary](FishburnTenSevenAuxiliary.md)
- Dependency: [D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenMinimum](FishburnTenSevenMinimum.md)
