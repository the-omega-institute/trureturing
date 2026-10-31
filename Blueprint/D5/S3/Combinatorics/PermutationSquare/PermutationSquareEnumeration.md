# Enumeration, generating series, and linear recurrence

## Abstract

Closed-form counts of indecomposable square-avoiders, the threshold of the conjectured recurrence, rational generating series over the integers, and the order-seven linear recurrence.

**Definition 1.1 (Compositions into parts at most four).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareEnumeration.boundedCompositions`

*Formalization.* `D5/S3/Combinatorics/PermutationSquare/PermutationSquareEnumeration.boundedCompositions` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

For every nonnegative n, boundedCompositions(n) is the set of lists of natural numbers whose entries each lie between one and four inclusive and sum to n.

**Definition 1.2 (Tetranacci composition count).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareEnumeration.c`

*Formalization.* `D5/S3/Combinatorics/PermutationSquare/PermutationSquareEnumeration.c` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

For every nonnegative n, c(n) is the cardinality of boundedCompositions(n), counting the compositions of n into parts of size one, two, three, or four.

**Definition 1.3 (Generating series of indecomposable square-avoiders).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareEnumeration.seriesB`

*Formalization.* `D5/S3/Combinatorics/PermutationSquare/PermutationSquareEnumeration.seriesB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

The formal power series over the integers whose coefficient of X to the n equals b(n) for every nonnegative integer n.

**Definition 1.4 (Generating series of nonempty square-avoiders).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareEnumeration.seriesA`

*Formalization.* `D5/S3/Combinatorics/PermutationSquare/PermutationSquareEnumeration.seriesA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

The formal power series over the integers with zero constant term whose coefficient of X to the n equals a(n) for every positive integer n.

**Theorem 1.5 (Exact indecomposable counts, composition convolution, and recurrence threshold).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareEnumeration.indecomposable_count_and_recurrence_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PermutationSquare/PermutationSquareEnumeration.indecomposable_count_and_recurrence_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

The sequence b(n) equals zero at n equal to zero, takes the values 1, 1, 2, 3, 3, 5, 6, 7 for n from one through eight, and equals floor(n / 2) plus four for every n at least nine. With c(0) equal to one, for every positive n the total count a(n) equals the convolution sum over k from one through n of b(k) times c(n minus k). For every n at least five, a(n) satisfies a(n) = a(n - 1) + a(n - 2) + a(n - 3) + a(n - 4) + b(n), so for every n at least six the identity a(n) = a(n - 1) + a(n - 2) + a(n - 3) + a(n - 4) + (n - 1) holds if and only if b(n) equals n minus one. Because b(n) equals n minus one for every n from six through ten and b(n) is strictly less than n minus one for every n at least eleven, for n at least six the identity a(n) = a(n - 1) + a(n - 2) + a(n - 3) + a(n - 4) + (n - 1) holds if and only if n is at most ten, whereas for every n at least eleven a(n) is strictly less than a(n - 1) + a(n - 2) + a(n - 3) + a(n - 4) + (n - 1).

**Theorem 1.6 (Rational generating series and the order-seven recurrence).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareEnumeration.generating_series_and_order_seven_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PermutationSquare/PermutationSquareEnumeration.generating_series_and_order_seven_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

Let num be X + X^4 - X^5 + X^6 + X^7 - X^8 - X^11, let denB be (1 - X)(1 - X^2), let denC be 1 - X - X^2 - X^3 - X^4, and let denA be the product denB times denC in formal power series over the integers. Both seriesB and seriesA have constant coefficient zero; denB, denC, and denA are units in the ring of integer formal power series; seriesA times denC equals seriesB so seriesA equals seriesB times the inverse of denC; seriesB times denB equals num so seriesB equals num times the inverse of denB; seriesA times denA equals num so seriesA equals num times the inverse of denA; denA expands to 1 - 2X - X^2 + 2X^3 + X^5 - X^7; and for every n at least twelve, over the integers, a(n) equals 2a(n - 1) + a(n - 2) - 2a(n - 3) - a(n - 5) + a(n - 7).

## References

- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareEnumeration.boundedCompositions`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareEnumeration.c`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareEnumeration.generating_series_and_order_seven_recurrence`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareEnumeration.indecomposable_count_and_recurrence_boundary`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareEnumeration.seriesA`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareEnumeration.seriesB`
- Dependency: [D5/S3/Combinatorics/PermutationSquare/PermutationSquareClassification](PermutationSquareClassification.md)
