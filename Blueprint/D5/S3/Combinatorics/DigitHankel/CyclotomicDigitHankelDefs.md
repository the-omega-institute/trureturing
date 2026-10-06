# Binary Digit Sums and Their Cyclotomic Hankel Zero Set

## Abstract

Binary Digit Sums and Their Cyclotomic Hankel Zero Set

**Definition 1.1 (Binary digit sum).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelDefs.digitSum`

*Formalization.* `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelDefs.digitSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

For a natural number u and a complex parameter t, digitSum is the sum of the binary digits of u, read from the least significant position, each multiplied by the corresponding power of t.

**Definition 1.2 (Binary digit Hankel determinant).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelDefs.hankel`

*Formalization.* `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelDefs.hankel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

For a natural number n and a complex parameter t, hankel is the determinant of the n by n matrix whose entry at indices i and j is digitSum of i plus j at t.

**Definition 1.3 (Cyclotomic interval radius).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelDefs.zBound`

*Formalization.* `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelDefs.zBound` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

For an order d and a length l, zBound uses the remainder of l minus one modulo d and its quotient by d to form the integer radius in the binary zero intervals.

**Definition 1.4 (Cyclotomic zero interval membership).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelDefs.InZeroSet`

*Formalization.* `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelDefs.InZeroSet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

A positive natural number n belongs to InZeroSet d when some l at least d plus one and some odd s place n in the half-open interval centered at 2 to the l times s with radius zBound d l plus one.

**Definition 1.5 (Cyclotomic Hankel zero characterization).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelDefs.claim`

*Formalization.* `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

For every d at least two, every primitive d-th root of unity zeta, and every n at least two, the binary digit Hankel determinant at 2 times zeta vanishes exactly when n belongs to InZeroSet d.

## References

- Truth anchor: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelDefs.InZeroSet`
- Truth anchor: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelDefs.digitSum`
- Truth anchor: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelDefs.hankel`
- Truth anchor: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelDefs.zBound`
