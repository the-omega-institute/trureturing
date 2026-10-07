# Vanishing Outside the Threshold Triples

## Abstract

Sparse binary kernel vectors force the Hankel determinant at t = -2 to vanish outside the threshold triples.

**Theorem 1.1 (Vanishing away from the triples).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelStructure.zero_direction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelStructure.zero_direction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

For every integer n at least two, if there is no nonnegative integer k for which n + 1 = n_k, n = n_k, or n = n_k + 1, then H(n,-2) = 0, where n_k = ceil(2^(k+2)/3). Splitting the binary digit sum into blocks gives sparse nonzero vectors in the kernel of the Hankel matrix at these sizes, forcing its determinant to vanish.

## References

- Truth anchor: `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelStructure.zero_direction`
- Dependency: [D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelDefs](BinaryDigitHankelDefs.md)
