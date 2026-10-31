# Explicit families and first-entry bounds

## Abstract

Seven explicit permutation families, prefix and position bounds on indecomposable square-avoiders, and the classifications for first entry two and first entry three.

**Definition 1.1 (Indecomposable square-avoiders).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.indecomposableAvoiders`

*Formalization.* `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.indecomposableAvoiders` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

For every nonnegative n, the set consists of the nonempty lists that permute one through n, avoid the classical patterns 312 and 54321, have squares avoiding the classical pattern 132, and are indecomposable under direct sum.

**Definition 1.2 (Indecomposable counting sequence).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.b`

*Formalization.* `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.b` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

For every nonnegative n, b(n) is the cardinality of the set of nonempty permutations of one through n that avoid 312 and 54321, have squares avoiding 132, and are indecomposable under direct sum.

**Definition 1.3 (The cyclic shift family I).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.familyI`

*Formalization.* `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.familyI` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

For a natural number n, familyI(n) lists the integers from two up to n in increasing order followed by one. For n at least two this is a permutation of one through n with first entry two.

**Definition 1.4 (The single-transposition family J).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.familyJ`

*Formalization.* `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.familyJ` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

For a natural number n, familyJ(n) begins with two, four, three, continues with five up to n in increasing order, and ends with one. For n at least five this is a permutation of one through n with first entry two.

**Definition 1.5 (The paired-inversion family K).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.familyK`

*Formalization.* `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.familyK` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

For natural numbers n and j, familyK(n, j) begins with two, lists j plus one adjacent descending pairs (2r + 5, 2r + 4) for r from zero through j, places three next, continues with 2j + 6 up to n in increasing order, and ends with one. For n at least six and j at most the floor of (n minus six) divided by two, this is a permutation of one through n with first entry two.

**Definition 1.6 (The monotone-middle family A).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.familyA`

*Formalization.* `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.familyA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

For a natural number n, familyA(n) begins with four, three, continues with five up to n in increasing order, and ends with two, one. For n at least six this is a permutation of one through n with first entry four.

**Definition 1.7 (The odd-offset paired family B).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.familyB`

*Formalization.* `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.familyB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

For a natural number n, familyB(n) begins with four, three, five, lists floor((n minus five) / 2) adjacent descending pairs (2r + 7, 2r + 6) starting from r equal to zero, and ends with two, one when n is odd and with two, n, one when n is even. For n at least seven this is a permutation of one through n with first entry four.

**Definition 1.8 (The even-offset paired family C).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.familyC`

*Formalization.* `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.familyC` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

For a natural number n, familyC(n) begins with four, three, lists floor((n minus four) / 2) adjacent descending pairs (2r + 6, 2r + 5) starting from r equal to zero, and ends with two, one when n is even and with two, n, one when n is odd. For n at least four this is a permutation of one through n with first entry four.

**Definition 1.9 (The exceptional prefix family D).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.familyD`

*Formalization.* `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.familyD` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

For a natural number n, familyD(n) begins with four, three, six, seven, five, continues with eight up to n in increasing order, and ends with two, one. For n at least nine this is a permutation of one through n with first entry four.

**Theorem 1.10 (Prefix criterion and structural bounds on indecomposable square-avoiders).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.indecomposable_shape_and_prefix_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.indecomposable_shape_and_prefix_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

The count b(0) vanishes, and for every positive n the nonempty condition in indecomposableAvoiders(n) is redundant because every permutation of one through n has length n. A permutation p of one through n is indecomposable under direct sum if and only if no proper positive prefix of length k maps one through k onto itself, and every permutation of one through n with n positive whose last entry is one is indecomposable. Moreover, for every n at least two and every p in indecomposableAvoiders(n) with first entry m, one-based position posN of the maximum entry n, and square q: p ends in one; m lies between two and four inclusive, every value from two through m minus one lies strictly right of position one, and the values from two through m minus one appear in strictly reverse order from left to right; q has value one at position posN, has value m at position n, increases strictly on positions after posN, and forces n + 1 <= posN + m together with posN >= n - m + 1, posN >= n - 3, and posN <= n - 1, with posN equal to n minus one whenever m equals two; and p decreases strictly on positions after posN.

**Theorem 1.11 (Membership and pairwise distinctness of the seven families).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.seven_families_admissible_and_distinct`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.seven_families_admissible_and_distinct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

Each of the seven explicit families belongs to indecomposableAvoiders(n) on its parameter domain: familyI(n) for n at least two, familyJ(n) for n at least five, familyK(n, j) for n at least six and j at most floor((n minus six) / 2), familyA(n) for n at least six, familyB(n) for n at least seven, familyC(n) for n at least four, and familyD(n) for n at least nine. On the domain of familyK, distinct indices j1 and j2 produce distinct permutations, and any two members chosen from distinct families among I, J, K, A, B, C, and D at the same length n on their common domain are distinct.

**Theorem 1.12 (Classification for first entry two and nonexistence for first entry three).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.first_entry_two_and_three_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.first_entry_two_and_three_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

For every natural number n at least four, an element p of indecomposableAvoiders(n) has first entry two if and only if p equals familyI(n), or n is at least five and p equals familyJ(n), or n is at least six and p equals familyK(n, j) for some j at most floor((n minus six) / 2); consequently the subset of indecomposableAvoiders(n) with first entry two has cardinality one when n equals four and floor(n / 2) when n is at least five. For every natural number n at least five, no element of indecomposableAvoiders(n) has first entry three.

## References

- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.b`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.familyA`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.familyB`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.familyC`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.familyD`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.familyI`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.familyJ`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.familyK`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.first_entry_two_and_three_classification`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.indecomposableAvoiders`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.indecomposable_shape_and_prefix_iff`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies.seven_families_admissible_and_distinct`
- Dependency: [D5/S3/Combinatorics/PermutationSquare/PermutationSquareCounting](PermutationSquareCounting.md)
