# Enumeration for 1132 and 2213

## Abstract

The generating function for nonnesting permutations avoiding 1132 and 2213 satisfies the stated quadratic equation.

**Theorem 1.1 (The 1132 and 2213 generating function).**

$$claim1132$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLow.result` (`✓ std3`). ∎

*Resolves.* `Problems/elizalde-luo-nonnesting-1132-2213` (proved) by `D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLow.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"elizalde-luo-nonnesting-1132-2213","declaration_gid":"D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLow.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Let R be the ordinary generating function counting doubled nonnesting permutations avoiding 1132 and 2213 by the number of distinct letters. Then xR squared - (1 - x) squared times R + (1 - x) squared equals zero.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLow.result`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalDownRuns](NonnestingBasicRoyalDownRuns.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalGround](NonnestingBasicRoyalGround.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalGroundSeries](NonnestingBasicRoyalGroundSeries.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingDefs](NonnestingDefs.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLowFiber](NonnestingRoyalLowFiber.md)
