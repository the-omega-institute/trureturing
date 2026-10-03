# Necessary Gaps at Ascents

## Abstract

Avoidance of 1132 and 2213 restricts the gaps between consecutive downsteps at ascents.

**Theorem 1.1 (Necessity of the gap condition).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLowGap.ascent_forces_good_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLowGap.ascent_forces_good_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Let a doubled nonnesting word avoid 1132 and 2213, have Dyck shape d, and have the same distinct-letter order p at its upsteps and downsteps. If consecutive downsteps correspond to an ascent of p, then the intervening sequence is empty or is a single upstep with the preceding prefix having one more upstep than downstep.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLowGap.ascent_forces_good_gap`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalBijection](NonnestingBasicRoyalBijection.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalBlocks](NonnestingBasicRoyalBlocks.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalShape](NonnestingBasicRoyalShape.md)
