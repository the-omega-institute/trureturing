# Permutation squares and the conjectured recurrence

## Abstract

Permutations avoiding 312 and 54321 whose squares avoid 132 define the counting sequence in the Archer-Bourne recurrence conjecture.

**Definition 1.1 (The square in one-line notation).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareDefs.square`

*Formalization.* `D5/S3/Combinatorics/PermutationSquare/PermutationSquareDefs.square` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

For a list p of natural numbers, replace each entry x by the entry of p at zero-based position x minus one, with zero as the default value when that position is absent. Subtraction is in the natural numbers. For a permutation of one through n, this gives its square under composition: the entry at position i is the value of p at position p(i).

**Definition 1.2 (The square-avoidance class).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareDefs.avoiders`

*Formalization.* `D5/S3/Combinatorics/PermutationSquare/PermutationSquareDefs.avoiders` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

For every nonnegative n, the set consists of the lists that permute one through n, avoid the classical patterns 312 and 54321, and have squares avoiding the classical pattern 132. Classical occurrence means a subsequence with the same relative order as the pattern.

**Definition 1.3 (The counting sequence).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareDefs.a`

*Formalization.* `D5/S3/Combinatorics/PermutationSquare/PermutationSquareDefs.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

For every nonnegative n, a(n) is the cardinality of the set of permutations of one through n that avoid 312 and 54321 and whose squares avoid 132.

**Definition 1.4 (The Archer-Bourne recurrence conjecture).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareDefs.claim`

*Formalization.* `D5/S3/Combinatorics/PermutationSquare/PermutationSquareDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

The conjecture in Section 5 of Archer and Bourne's Pattern avoidance in compositions and powers of permutations states that, for every natural number n at least six, a(n) equals a(n minus one) plus a(n minus two) plus a(n minus three) plus a(n minus four) plus n minus one. Here a(n) counts permutations avoiding 312 and 54321 whose squares avoid 132.

## References

- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareDefs.a`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareDefs.avoiders`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareDefs.square`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingDefs](../Nonnesting/NonnestingDefs.md)
