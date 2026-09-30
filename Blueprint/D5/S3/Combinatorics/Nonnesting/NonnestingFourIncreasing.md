# Structure with Increasing First Occurrences

## Abstract

Adjacent letters and value cuts constrain increasing-order avoiders.

**Theorem 1.1 (Adjacent positions of consecutive letters).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingFourIncreasing.increasing_adjacent`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingFourIncreasing.increasing_adjacent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

In an increasing-order avoider, the second occurrence of i and the first occurrence of i plus one occupy adjacent positions.

**Theorem 1.2 (The first three letters).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingFourIncreasing.increasing_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingFourIncreasing.increasing_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

For size at least two, an increasing-order avoider begins either 112 or 121.

**Theorem 1.3 (Cut criterion for consecutive letters).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingFourIncreasing.increasing_cut_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingFourIncreasing.increasing_cut_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

In an increasing-order avoider, a value cut at i occurs exactly when the second i precedes the first i plus one.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingFourIncreasing.increasing_adjacent`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingFourIncreasing.increasing_cut_iff`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingFourIncreasing.increasing_prefix`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicCuts](NonnestingBasicCuts.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicDeletion](NonnestingBasicDeletion.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveThree](NonnestingFourPrimitiveThree.md)
