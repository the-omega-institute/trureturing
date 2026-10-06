# Reflection and Block Conjugation

## Abstract

Reflection and Block Conjugation

**Theorem 1.1 (Determinant-one block conjugation).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelReflection.block_conjugation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelReflection.block_conjugation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

For a sequence over a commutative ring satisfying the two binary carry relations, with 2 to the k below n at most twice that power, there is a determinant-one matrix whose conjugation transforms the Hankel matrix into the stated binary block form with weights w and x minus 2w.

**Theorem 1.2 (Weighted reflection recurrence).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelReflection.weighted_reflection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelReflection.weighted_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

Under the carry relations, k at least one, and n in the reflection range, the Hankel determinant H at n and bordered determinant E at n reduce to the corresponding determinants at 2 to the k plus reflected index, with the explicit powers and signs in the recurrence.

## References

- Truth anchor: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelReflection.block_conjugation`
- Truth anchor: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelReflection.weighted_reflection`
- Dependency: [D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelRecurrence](BinaryDigitHankelRecurrence.md)
