# The corrected counting recurrence

## Abstract

Removing the final decreasing component gives a four-term recurrence with the number of indecomposable square-avoiders as its additional term.

**Theorem 1.1 (Counting by the final component).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareCounting.count_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PermutationSquare/PermutationSquareCounting.count_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

For every natural number n at least five, a(n) equals a(n minus one) plus a(n minus two) plus a(n minus three) plus a(n minus four) plus b(n), where b(n) counts the permutations of one through n that avoid 312 and 54321, have squares avoiding 132, and are indecomposable under direct sum. Each decomposable permutation has a final decreasing component of length one, two, three or four; deleting it leaves a nonempty permutation in the same square-avoidance class. These four possibilities and the indecomposable permutations partition the class.

## References

- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareCounting.count_recurrence`
- Dependency: [D5/S3/Combinatorics/PermutationSquare/PermutationSquareStructure](PermutationSquareStructure.md)
