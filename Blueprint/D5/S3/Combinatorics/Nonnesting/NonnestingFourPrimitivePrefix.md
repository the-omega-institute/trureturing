# Patterns under a Largest-Letter Prefix

## Abstract

Occurrences under a doubled largest prefix reduce to the tail or a smaller obstruction.

**Theorem 1.1 (Nesting patterns reduce to the tail).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitivePrefix.prefix_nesting_reduces`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitivePrefix.prefix_nesting_reduces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

A 1221 or 2112 occurrence in a doubled-largest-prefix word already occurs in its tail.

**Theorem 1.2 (Four-pattern occurrence reduction).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitivePrefix.prefix_pattern_reduces`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitivePrefix.prefix_pattern_reduces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

An occurrence of one of the four forbidden patterns in a doubled-largest-prefix word occurs in the tail or gives a descending three-letter sublist with its larger letter repeated.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitivePrefix.prefix_nesting_reduces`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitivePrefix.prefix_pattern_reduces`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveLarge](NonnestingFourPrimitiveLarge.md)
