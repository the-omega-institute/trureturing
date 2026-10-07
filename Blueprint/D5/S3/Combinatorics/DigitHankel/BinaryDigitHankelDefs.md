# Weighted Binary Digit Sums and Hankel Determinants

## Abstract

Weighted binary digit sums define Hankel determinants whose nonvanishing indices at t = -2 are triples around the numbers ceil(2^(k+2)/3).

**Definition 1.1 (The weighted binary digit sum).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelDefs.digitSum`

*Formalization.* `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelDefs.digitSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

For a nonnegative integer u with binary expansion u = sum_j epsilon_j 2^j and an integer t, S(u,t) = sum_j epsilon_j t^j, where each epsilon_j is zero or one. The sum is finite, and S(0,t) = 0.

**Definition 1.2 (The binary digit Hankel determinant).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelDefs.hankel`

*Formalization.* `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelDefs.hankel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

For a nonnegative integer n and an integer t, H(n,t) is the determinant of the n by n integer matrix with entry S(i+j,t) in row i and column j, where i and j range from zero to n minus one. The determinant of the empty matrix is one.

**Definition 1.3 (The centers of the index triples).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelDefs.threshold`

*Formalization.* `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelDefs.threshold` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

For every nonnegative integer k, n_k = ceil(2^(k+2)/3), equivalently the integer quotient (2^(k+2) + 2)/3. The sequence begins 2, 3, 6, 11, 22, 43.

**Definition 1.4 (The nonvanishing equivalence at minus two).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelDefs.claim`

*Formalization.* `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

For every integer n at least two, H(n,-2) is nonzero if and only if there is a nonnegative integer k such that n + 1 = n_k, n = n_k, or n = n_k + 1, with n_k = ceil(2^(k+2)/3). This is the case d = 2 of Conjecture 5.7 in Section 5.1 of Sobolewski and Ulas's paper.

## References

- Truth anchor: `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelDefs.digitSum`
- Truth anchor: `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelDefs.hankel`
- Truth anchor: `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelDefs.threshold`
