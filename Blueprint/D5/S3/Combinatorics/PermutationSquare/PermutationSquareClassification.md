# First entry four and complete classification

## Abstract

Tail structure, middle-segment pattern avoidance, classification for first entry four across all lengths at least four, and the full seven-family classification for lengths at least nine.

**Theorem 1.1 (Tail types and middle-segment structure when the first entry is four).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareClassification.first_entry_four_structure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PermutationSquare/PermutationSquareClassification.first_entry_four_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

For every natural number n at least four and every p in indecomposableAvoiders(n) with first entry four, the last four entries of the square of p form a permutation of one, two, three, four ending in four, and the three entries of p immediately preceding its final entry one form the set consisting of n together with the one-based positions of two and three in p. When n is at least five, the second entry of p equals three and those three penultimate entries form one of the triples (n, n minus one, two), (n minus one, n, two), or (n minus two, two, n). When n is at least seven, the middle subword M of length n minus six starting at the third entry of p avoids both 312 and 321; its set of entries equals five through n minus two in the first two tail cases, while in the third tail case its set of entries equals five through n minus three together with n minus one and the entry immediately before the triple equals n minus one.

**Theorem 1.2 (Classification and count for first entry four).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareClassification.first_entry_four_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PermutationSquare/PermutationSquareClassification.first_entry_four_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

For every natural number n at least four, a list p belongs to indecomposableAvoiders(n) and has first entry four if and only if p equals familyC(n), or n is at least six and p equals familyA(n), or n is at least seven and p equals familyB(n), or n is at least nine and p equals familyD(n). Consequently, the number of indecomposable square-avoiders of length n with first entry four equals one for n equal to four or five, two for n equal to six, three for n equal to seven or eight, and four for every n at least nine.

**Theorem 1.3 (Complete classification of indecomposable square-avoiders for length at least nine).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareClassification.indecomposable_classification_ge_nine`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PermutationSquare/PermutationSquareClassification.indecomposable_classification_ge_nine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

For every natural number n at least nine, a list p belongs to indecomposableAvoiders(n) if and only if p equals familyI(n), familyJ(n), familyK(n, j) for some j at most floor((n minus six) / 2), familyA(n), familyD(n), familyB(n), or familyC(n).

## References

- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareClassification.first_entry_four_classification`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareClassification.first_entry_four_structure`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareClassification.indecomposable_classification_ge_nine`
- Dependency: [D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies](PermutationSquareFamilies.md)
