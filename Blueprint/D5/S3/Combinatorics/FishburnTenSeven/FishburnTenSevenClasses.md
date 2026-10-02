# FishburnTenSevenClasses

## Abstract

Relative orders between three monotone blocks characterize two triple-avoidance classes.

**Theorem 1.1 (Avoidance conditions on three blocks).**

Lean statement: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenClasses.shape_classes_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenClasses.shape_classes_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Let D followed by one, I, a peak, and J be a permutation of one through n, with D and J decreasing, I increasing, and every entry of I and J below the peak. It is a Fishburn permutation avoiding 1324, 2143 and 1423 if and only if no entry t of J has t plus one in I and every entry of J is below every entry of D. It is a Fishburn permutation avoiding 1324, 1423 and 3124 if and only if the same successor condition holds and every entry of D below the peak is below every entry of I.

## References

- Truth anchor: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenClasses.shape_classes_iff`
- Dependency: [D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenShape](FishburnTenSevenShape.md)
