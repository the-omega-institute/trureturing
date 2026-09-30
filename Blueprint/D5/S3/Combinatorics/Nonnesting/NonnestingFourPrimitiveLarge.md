# Removing the Doubled Largest Prefix

## Abstract

The largest-letter prefix is primitive and leaves an ordered avoider.

**Theorem 1.1 (Primitivity of the largest prefix).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveLarge.primitive_large_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveLarge.primitive_large_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

A word beginning with two copies of its largest letter has no proper value cut.

**Theorem 1.2 (Tail after the largest prefix).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveLarge.large_first_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveLarge.large_first_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Removing the two initial largest letters from such an avoider leaves an avoider of size one less with increasing first-occurrence order.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveLarge.large_first_tail`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveLarge.primitive_large_prefix`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingFourLargeFirst](NonnestingFourLargeFirst.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveIncUnique](NonnestingFourPrimitiveIncUnique.md)
