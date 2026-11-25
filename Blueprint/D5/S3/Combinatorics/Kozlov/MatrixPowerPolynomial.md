# Polynomial entries of upper unitriangular matrix powers

## Abstract

Writing a unitriangular matrix as the identity plus a strictly upper triangular matrix gives a finite binomial expansion of its powers.

**Definition 1.1 (The part off the diagonal).**

Lean statement: `D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial.offDiag`

*Formalization.* `D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial.offDiag` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Keep the original entries away from the diagonal and put zero on the diagonal.

**Theorem 1.2 (Split off the identity matrix).**

Lean statement: `D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial.one_add_offDiag`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial.one_add_offDiag` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The diagonal-one hypothesis supplies equality on the diagonal and the other entries are unchanged.

**Theorem 1.3 (Powers impose increasing state distance).**

Lean statement: `D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial.pow_apply_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial.pow_apply_eq_zero` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Every nonzero term in matrix multiplication traverses a strictly increasing chain of indices. Induct on the exponent.

**Theorem 1.4 (Strict triangularity gives nilpotence).**

Lean statement: `D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial.pow_eq_zero_of_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial.pow_eq_zero_of_le` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

No chain of the required length can fit in the finite index range once the exponent reaches its size.

**Theorem 1.5 (The finite binomial expansion of powers).**

Lean statement: `D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial.pow_eq_sum_choose`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial.pow_eq_sum_choose` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The identity commutes with the off-diagonal part. Apply the binomial theorem and discard the vanishing powers beyond the matrix size.

**Definition 1.6 (The rational polynomial of one power entry).**

Lean statement: `D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial.powerPolynomial`

*Formalization.* `D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial.powerPolynomial` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Sum the entries of the off-diagonal powers against the falling-binomial polynomials, through the last possibly nonzero power.

**Theorem 1.7 (Natural evaluations recover matrix power entries).**

Lean statement: `D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial.powerPolynomial_eval`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial.powerPolynomial_eval` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

At a natural input each falling-binomial polynomial evaluates to the corresponding binomial coefficient. The finite matrix expansion then yields the desired entry.

## References

- Truth anchor: `D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial.offDiag`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial.one_add_offDiag`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial.pow_apply_eq_zero`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial.pow_eq_sum_choose`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial.pow_eq_zero_of_le`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial.powerPolynomial`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial.powerPolynomial_eval`
