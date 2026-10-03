# Combined Dyck Weights

## Abstract

Adjacent downsteps and later singleton components contribute to the same weight.

**Definition 1.1 (Combined weight sum).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalGroundCount.groundWeight`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalGroundCount.groundWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

For semilength n, sum over all Dyck paths two to the power of the number of adjacent downstep pairs plus the number of ground-level singleton components after the first component.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalGroundCount.groundWeight`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalDownCount](NonnestingBasicRoyalDownCount.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalGround](NonnestingBasicRoyalGround.md)
