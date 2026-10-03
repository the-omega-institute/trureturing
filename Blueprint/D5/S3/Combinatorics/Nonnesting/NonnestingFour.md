# Enumeration for Four Forbidden Patterns

## Abstract

The four-pattern avoidance class has the asserted rational generating function.

**Theorem 1.1 (Four-pattern generating function).**

$$claimFour$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingFour.result` (`✓ std3`). ∎

*Resolves.* `Problems/elizalde-luo-nonnesting-1231-1312-2231-3221` (proved) by `D5/S3/Combinatorics/Nonnesting/NonnestingFour.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"elizalde-luo-nonnesting-1231-1312-2231-3221","declaration_gid":"D5/S3/Combinatorics/Nonnesting/NonnestingFour.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

The ordinary generating function for doubled nonnesting permutations avoiding 1231, 1312, 2231, and 3221 is (1 - 3x + 2x squared) divided by (1 - 3x)(1 - x - x squared).

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingFour.result`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveClassify](NonnestingFourPrimitiveClassify.md)
