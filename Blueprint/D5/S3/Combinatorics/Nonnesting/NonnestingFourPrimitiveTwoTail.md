# The Tail after an Initial Two

## Abstract

Deleting the first two values recovers a smaller primitive increasing-order word.

**Theorem 1.1 (Primitive tail decomposition).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveTwoTail.primitive_two_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveTwoTail.primitive_two_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

For a primitive avoider beginning with two, filtering letters above two and subtracting two gives a smaller primitive increasing-order avoider, and the original word has the specified 21321 prefix.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveTwoTail.primitive_two_tail`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicDeletion](NonnestingBasicDeletion.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveTwoPrefix](NonnestingFourPrimitiveTwoPrefix.md)
