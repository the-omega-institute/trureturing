# Hook-Block Decomposition

## Abstract

Permutations avoiding 123 and 132 decompose into hook-shaped blocks.

**Definition 1.1 (Hook-block permutation).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalHookBlocks.hookBlocks`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalHookBlocks.hookBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

For a block of size k with largest remaining value n, list n minus one down through n minus k plus one, followed by n. Concatenate this block with the blocks constructed from the remaining sizes and the remaining largest value n minus k.

**Theorem 1.2 (Existence of hook blocks).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalHookBlocks.avoids_has_hook_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalHookBlocks.avoids_has_hook_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Every permutation of one through n avoiding 123 and 132 is a concatenation of hook-shaped blocks whose positive sizes sum to n.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalHookBlocks.avoids_has_hook_blocks`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalHookBlocks.hookBlocks`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalHooks](NonnestingBasicRoyalHooks.md)
