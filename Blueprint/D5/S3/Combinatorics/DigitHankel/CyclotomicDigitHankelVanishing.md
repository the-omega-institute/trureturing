# Sparse Kernels at Cyclotomic Parameters

## Abstract

Sparse Kernels at Cyclotomic Parameters

**Theorem 1.1 (Sparse kernel interval criterion).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelVanishing.sparse_kernel_interval`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelVanishing.sparse_kernel_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

If two finitely supported coefficient sequences have the stated support, nonzero witnesses, zero total sum, and both digit-sum convolution identities, then the Hankel determinant at the indicated size and parameter t is zero.

**Theorem 1.2 (Odd carry kernel).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelVanishing.odd_carry_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelVanishing.odd_carry_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

For a field of characteristic zero, if f changes by one between every even and following odd index, then every positive odd size has a nonzero vector in the kernel of the corresponding carry-difference matrix.

**Theorem 1.3 (Root base kernel).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelVanishing.root_base_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelVanishing.root_base_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

For positive d and k and a parameter zeta with zeta to the d equal to one, there is a coefficient sequence beginning with one, vanishing on the final prescribed interval, summing to zero, and annihilating the digit-sum Hankel rows together with the odd carry rows.

**Theorem 1.4 (Root second kernel).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelVanishing.root_second_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelVanishing.root_second_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

For positive d and a parameter zeta with zeta to the d equal to one, there is a coefficient sequence beginning with one, vanishing on the final interval of length 2 to the d minus one, summing to zero, and annihilating every digit-sum Hankel row through size 2 to the 2d.

## References

- Truth anchor: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelVanishing.odd_carry_kernel`
- Truth anchor: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelVanishing.root_base_kernel`
- Truth anchor: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelVanishing.root_second_kernel`
- Truth anchor: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelVanishing.sparse_kernel_interval`
- Dependency: [D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelStructure](BinaryDigitHankelStructure.md)
- Dependency: [D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelDefs](CyclotomicDigitHankelDefs.md)
