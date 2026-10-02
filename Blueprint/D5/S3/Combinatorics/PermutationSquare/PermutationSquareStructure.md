# The first component and the layered tail

## Abstract

A nonempty permutation avoiding 312 and 54321 whose square avoids 132 consists of an indecomposable first component followed by decreasing components of length at most four.

**Theorem 1.1 (The last entry of an indecomposable component).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareStructure.component_ends_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PermutationSquare/PermutationSquareStructure.component_ends_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

Every nonempty permutation of one through its length that avoids 312 and is indecomposable under direct sum ends in one. Direct-sum indecomposability means that at every proper nonempty prefix there is an entry in the remaining suffix no greater than some entry of the prefix.

**Theorem 1.2 (Squaring a direct sum and its tail).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareStructure.square_tail_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PermutationSquare/PermutationSquareStructure.square_tail_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

Let left and right be permutations of one through m and one through n, respectively, with m positive. Their direct sum is left followed by right with m added to every entry. Its square is the direct sum of their squares. If the square of the direct sum avoids 132, the square of right is the increasing permutation of one through n, so right is an involution.

**Theorem 1.3 (Indecomposable 312-avoiding involutions are decreasing).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareStructure.component_involution_decreasing`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PermutationSquare/PermutationSquareStructure.component_involution_decreasing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

If a nonempty permutation of one through its length avoids 312, is indecomposable under direct sum, and has square equal to the increasing permutation, then it is the decreasing permutation of that length.

**Theorem 1.4 (Decomposition of a square-avoider).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareStructure.avoider_layered_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PermutationSquare/PermutationSquareStructure.avoider_layered_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

For every positive n, each permutation p of one through n avoiding 312 and 54321 whose square avoids 132 is a direct sum of a nonempty indecomposable first component and a list of decreasing blocks. The first component belongs to the same square-avoidance class at its own length. Every block of the tail is nonempty, consists of its length down to one, and has length at most four. The tail is assembled by repeated direct sums and may be empty.

**Theorem 1.5 (Appending decreasing blocks preserves square avoidance).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareStructure.admissible_layered_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PermutationSquare/PermutationSquareStructure.admissible_layered_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

Let first be a nonempty permutation avoiding 312 and 54321 whose square avoids 132. Let tail be any list of nonempty decreasing permutations, each of length at most four. The direct sum of first with the repeated direct sum of tail again avoids 312 and 54321 and has square avoiding 132. The first permutation need not be indecomposable.

## References

- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareStructure.admissible_layered_tail`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareStructure.avoider_layered_tail`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareStructure.component_ends_one`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareStructure.component_involution_decreasing`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareStructure.square_tail_identity`
- Dependency: [D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicComponents](../FishburnTenThirteen/FishburnBasicComponents.md)
- Dependency: [D5/S3/Combinatorics/PermutationSquare/PermutationSquareDefs](PermutationSquareDefs.md)
