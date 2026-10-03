# Compositions for a Fixed Dyck Shape

## Abstract

Permitted ascent positions parametrize the avoiders of a fixed Dyck shape.

**Definition 1.1 (Permitted ascent positions).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLowFiber.goodPositions`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLowFiber.goodPositions` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Among the indices less than n minus one, retain those for which every separation of the corresponding consecutive downsteps in d is empty or consists of a single upstep with the preceding prefix having one more upstep than downstep.

**Definition 1.2 (Fixed-shape composition equivalence).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLowFiber.lowFiberEncoding`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLowFiber.lowFiberEncoding` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

For a Dyck path d of semilength n, compositions of n whose increasing-block permutation has ascents only at permitted positions correspond bijectively to doubled nonnesting permutations of shape d avoiding 1132 and 2213.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLowFiber.goodPositions`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLowFiber.lowFiberEncoding`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalBijection](NonnestingBasicRoyalBijection.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalBlocks](NonnestingBasicRoyalBlocks.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalIncConverse](NonnestingBasicRoyalIncConverse.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalShape](NonnestingBasicRoyalShape.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLowConverse](NonnestingRoyalLowConverse.md)
