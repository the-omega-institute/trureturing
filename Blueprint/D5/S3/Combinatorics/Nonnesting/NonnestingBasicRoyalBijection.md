# Permutation and Dyck-Path Encoding

## Abstract

A permutation and a Dyck path specify a doubled nonnesting permutation.

**Definition 1.1 (Permutation and path pairs).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalBijection.royalPairs`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalBijection.royalPairs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

A pair consists of a permutation of the letters from one through n and a Dyck path whose semilength equals the length of that permutation.

**Definition 1.2 (Interleaving equivalence).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalBijection.royalEncoding`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalBijection.royalEncoding` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Pairs of a permutation of one through n and a Dyck path of semilength n correspond bijectively to doubled nonnesting permutations. Read the permutation once along the upsteps and once along the downsteps.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalBijection.royalEncoding`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalBijection.royalPairs`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalShape](NonnestingBasicRoyalShape.md)
