# Ordering after the First Primitive Block

## Abstract

A later inversion creates a cut, restricting primitive words.

**Theorem 1.1 (A later inversion forces a cut).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveBlocks.later_inversion_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveBlocks.later_inversion_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

If first occurrences before t are separated from later values but a larger c precedes t, an avoider has a value cut at t minus one.

**Theorem 1.2 (Order after an initial one or two).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveBlocks.primitive_later_order`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveBlocks.primitive_later_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

A primitive avoider beginning with one or two has increasing first-occurrence order among letters from two through n.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveBlocks.later_inversion_cut`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveBlocks.primitive_later_order`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicCuts](NonnestingBasicCuts.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveLargeConverse](NonnestingFourPrimitiveLargeConverse.md)
