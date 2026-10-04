# Paired Reflection Recurrences

## Abstract

Binary-carry reflection relates the Hankel determinant and a bordered difference determinant at complementary sizes.

**Definition 1.1 (The bordered difference determinant).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelRecurrence.endpoint`

*Formalization.* `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelRecurrence.endpoint` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

For a nonnegative integer n and an integer t, E(n,t) is the determinant of the n by n matrix whose entry in row i and column j is S(i+j+1,t) - S(i+j,t) when j + 1 is less than n, and is one in the final column. Indices range from zero to n minus one. The determinant of the empty matrix is one.

**Theorem 1.2 (Reflection of both determinants).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelRecurrence.reflection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelRecurrence.reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

For integers k at least one and n at least five satisfying 2^k < n and n at most 3 times 2^(k-1), and every integer t, put m = 2^(k+1) - n + 1, a = 2n - 2^(k+1) - 1, and u = t^(k+1) - 2t^k. Then H(n,t) = (-1)^(n+1) u^a H(m,t) + (t^k)^2 u^(a-1) E(m,t), and E(n,t) = (-1)^n u^a E(m,t). Here a is at least one. A binary-carry change of basis of determinant one gives a sparse matrix, and paired elimination yields both identities without dividing by u.

## References

- Truth anchor: `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelRecurrence.endpoint`
- Truth anchor: `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelRecurrence.reflection`
- Dependency: [D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelStructure](BinaryDigitHankelStructure.md)
