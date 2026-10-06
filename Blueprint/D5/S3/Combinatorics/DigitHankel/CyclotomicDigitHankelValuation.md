# Valuation Bounds and Recursive Noncancellation

## Abstract

Valuation Bounds and Recursive Noncancellation

**Theorem 1.1 (Torsion root difference valuation).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelValuation.torsion_root_difference`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelValuation.torsion_root_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

For a valuation in which the value of 2 is below one, a nontrivial n-th root of unity has difference from one of valuation at least the value of 2, with equality exactly for the root minus one.

**Theorem 1.2 (Recursive noncancellation).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelValuation.recursive_noncancellation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelValuation.recursive_noncancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

Assume base bounds through size four, equality information at valuation one, and a recursive determinant step whose correction term has strictly smaller valuation. Then every nonzero bordered determinant forces the corresponding Hankel determinant to be nonzero and preserves the valuation lower bound.

## References

- Truth anchor: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelValuation.recursive_noncancellation`
- Truth anchor: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelValuation.torsion_root_difference`
- Dependency: [D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelRecurrence](BinaryDigitHankelRecurrence.md)
