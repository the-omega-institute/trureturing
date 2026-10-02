# FishburnTenSevenShape

## Abstract

The Fishburn condition on a three-block permutation is a restriction on successive values.

**Theorem 1.1 (Fishburn condition for the block form).**

Lean statement: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenShape.shape_fishburn_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenShape.shape_fishburn_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Let D followed by one, I, a peak, and J be a permutation of one through n, with D and J decreasing, I increasing, and every entry of I and J below the peak. This permutation is Fishburn if and only if no entry t of J has t plus one in I.

## References

- Truth anchor: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenShape.shape_fishburn_iff`
- Dependency: [D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenMinimum](FishburnTenSevenMinimum.md)
- Dependency: [D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenUnimodal](FishburnTenSevenUnimodal.md)
