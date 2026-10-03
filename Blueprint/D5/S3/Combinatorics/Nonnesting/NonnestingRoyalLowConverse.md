# Avoidance from Permitted Gaps

## Abstract

The increasing-block order and permitted Dyck gaps imply avoidance of 1132 and 2213.

**Theorem 1.1 (Sufficiency of the gap condition).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLowConverse.good_gaps_avoid_low`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLowConverse.good_gaps_avoid_low` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Let a doubled nonnesting word have Dyck shape d and the same distinct-letter order p at its upsteps and downsteps. Suppose p avoids 132 and 213. Whenever consecutive downsteps in d correspond to an ascent of p, require either that they are adjacent or that they enclose a single upstep with the preceding prefix having one more upstep than downstep. Then the word avoids 1132 and 2213.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLowConverse.good_gaps_avoid_low`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalBijection](NonnestingBasicRoyalBijection.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalBlocks](NonnestingBasicRoyalBlocks.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalShape](NonnestingBasicRoyalShape.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLowGap](NonnestingRoyalLowGap.md)
