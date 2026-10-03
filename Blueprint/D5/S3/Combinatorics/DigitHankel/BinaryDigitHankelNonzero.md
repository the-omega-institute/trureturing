# Evaluations on the Threshold Triples

## Abstract

Reflection induction evaluates the binary digit Hankel determinants at each center and its two adjacent indices.

**Theorem 1.1 (The two adjacent determinant families).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelNonzero.endpoint_evaluations`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelNonzero.endpoint_evaluations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

For every integer k at least two, put n_k = ceil(2^(k+2)/3). Then H(n_k-1,-2) = -2^((k+1)n_k - floor(3k/2) - 4) and H(n_k+1,-2) = 2^((k+1)n_k + floor(k/2) + 2 - (k mod 2)). Moreover E(n_k-1,-2) = 0 and E(n_k+1,-2) = 0. The initial values at k = 2 and the paired reflection recurrences give a simultaneous induction: reflection interchanges the two adjacent families, while the vanishing of E removes the additive term in the recurrence for H.

**Theorem 1.2 (The determinant families at the centers).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelNonzero.center_evaluations`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelNonzero.center_evaluations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

For every nonnegative integer k, put n_k = ceil(2^(k+2)/3). Then E(n_k,-2) = (-1)^k 2^((k+1)n_k - floor((k+1)/2)) and 12 H(n_k,-2) = -(2^(k+1) + (-1)^k) E(n_k,-2). Reflection sends the center n_k to the preceding center for k at least two. The initial values at k = 0 and k = 1 and simultaneous induction give the two identities.

## References

- Truth anchor: `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelNonzero.center_evaluations`
- Truth anchor: `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelNonzero.endpoint_evaluations`
- Dependency: [D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelRecurrence](BinaryDigitHankelRecurrence.md)
- Dependency: [D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelStructure](BinaryDigitHankelStructure.md)
