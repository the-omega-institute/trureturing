# Increasing-Block Decomposition

## Abstract

Permutations avoiding 132 and 213 decompose into increasing blocks with decreasing value ranges.

**Definition 1.1 (Increasing-block permutation).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalIncBlocks.incBlocks`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalIncBlocks.incBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

For a block of size k with largest remaining value n, list n minus k plus one through n in increasing order. Concatenate this block with the blocks constructed from the remaining sizes and the remaining largest value n minus k.

**Theorem 1.2 (Existence of increasing blocks).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalIncBlocks.avoids_has_inc_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalIncBlocks.avoids_has_inc_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Every permutation of one through n avoiding 132 and 213 is a skew sum of increasing blocks whose positive sizes sum to n.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalIncBlocks.avoids_has_inc_blocks`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalIncBlocks.incBlocks`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalBlocks](NonnestingBasicRoyalBlocks.md)
