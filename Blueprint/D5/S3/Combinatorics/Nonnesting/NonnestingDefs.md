# Nonnesting Avoidance and Generating Functions

## Abstract

Doubled-word avoidance classes and their generating-function identities are defined.

**Definition 1.1 (Number of pattern letters).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.letters`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.letters` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

The largest letter appearing in a pattern specifies its ordered alphabet.

**Definition 1.2 (Pattern occurrence).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.Occurs`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.Occurs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

A pattern occurs in a word when an ordered relabeling of the pattern is a subsequence of that word.

**Definition 1.3 (Nonnesting pattern avoiders).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.avoiders`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.avoiders` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

An avoider is a permutation of two copies of each letter from one through n that avoids 1221, 2112, and every listed pattern.

**Definition 1.4 (Ordinary generating function).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.gf`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.gf` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

The coefficient of degree n is the number of avoiders of size n.

**Definition 1.5 (Single-pattern counting identity).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.claim1322`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.claim1322` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

For every positive n, n times the number of 1322 avoiders equals a finite sum of products of binomial coefficients.

**Definition 1.6 (Quadratic power-series identity).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.IsRoyalRoot`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.IsRoyalRoot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

A power series satisfies the quadratic equation x times its square minus the square of one minus x times the series plus that square equals zero.

**Definition 1.7 (The 1132 and 2213 identity).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.claim1132`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.claim1132` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

The generating function for avoiding 1132 and 2213 satisfies the quadratic power-series identity.

**Definition 1.8 (The 1233 and 1322 identity).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.claim1233`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.claim1233` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

The generating function for avoiding 1233 and 1322 satisfies the same quadratic power-series identity.

**Definition 1.9 (The four-pattern rational identity).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.claimFour`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.claimFour` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

The generating function for avoiding 1231, 1312, 2231, and 3221, multiplied by (1 - 3x)(1 - x - x squared), equals 1 - 3x + 2x squared.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.IsRoyalRoot`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.Occurs`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.avoiders`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.claim1132`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.claim1233`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.claim1322`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.claimFour`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.gf`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingDefs.letters`
- Dependency: [D5/S3/Combinatorics/ArrowWilfDefs](../ArrowWilfDefs.md)
