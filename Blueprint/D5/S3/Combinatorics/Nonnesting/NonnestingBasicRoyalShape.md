# Dyck Shape of a Doubled Word

## Abstract

Parity of the preceding multiplicities determines the step sequence of a doubled word.

**Definition 1.1 (Occurrence-parity scan).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalShape.scan`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalShape.scan` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Start with a set of active letters. For each letter, record a downstep if it is active and an upstep otherwise, then toggle its membership in the active set.

**Definition 1.2 (Dyck shape).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalShape.shape`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalShape.shape` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

For a word obtained by permuting a list containing two copies of each entry of a given letter list, scanning from the empty active set produces a Dyck path.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalShape.scan`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalShape.shape`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalEncoding](NonnestingBasicRoyalEncoding.md)
