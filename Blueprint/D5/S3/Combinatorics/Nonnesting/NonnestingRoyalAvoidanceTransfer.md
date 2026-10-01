# Transfer Between Two Avoidance Classes

## Abstract

Reversed occurrence positions transfer avoidance between the two pairs of patterns.

**Theorem 1.1 (Avoidance under occurrence reversal).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingRoyalAvoidanceTransfer.avoidance_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingRoyalAvoidanceTransfer.avoidance_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Let positive block sizes sum to n. Let w and v be doubled nonnesting words whose first-occurrence orders are respectively the increasing-block permutation and the hook-block permutation with reversed block sizes. Suppose, for each index i less than n, the first position of the reversed-index hook letter in v plus the second position of the corresponding increasing-block letter in w plus one equals the length of w, and the same equality holds with first and second positions exchanged. Then w avoids 1132 and 2213 if and only if v avoids 1233 and 1322.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingRoyalAvoidanceTransfer.avoidance_transfer`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalBijection](NonnestingBasicRoyalBijection.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalHookBlocks](NonnestingBasicRoyalHookBlocks.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalIncConverse](NonnestingBasicRoyalIncConverse.md)
