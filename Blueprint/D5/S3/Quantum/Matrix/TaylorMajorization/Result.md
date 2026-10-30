# Refutation of unrestricted Hermitian Taylor majorization.

## Abstract

Refutation of unrestricted Hermitian Taylor majorization.

**Theorem 1.1 (The spectral comparison is false).**

Lean statement: `D5/S3/Quantum/Matrix/TaylorMajorization/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TaylorMajorization/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhang-2026-taylor-coefficient-weak-majorization` (refuted) by `D5/S3/Quantum/Matrix/TaylorMajorization/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhang-2026-taylor-coefficient-weak-majorization","declaration_gid":"D5/S3/Quantum/Matrix/TaylorMajorization/Result.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* T. Zhang (2026). *Weak majorization inequalities for the cubic and quartic coefficients of e^{(A+B)t} versus e^{At}e^{Bt}*. DOI: [10.48550/arXiv.2601.07286](https://doi.org/10.48550/arXiv.2601.07286). URL: <https://arxiv.org/abs/2601.07286>.

*Commentary.*

The claim for all Hermitian matrices and every order at least five is false. Use dimension two, A=Z-I, B=X and order five. Both matrices are Hermitian. Weak majorization would imply the real trace inequality by the full initial sum. The shifted Pauli family instead gives a strictly negative trace defect, contradicting that inequality. The example concerns Hermitian matrices without a positivity restriction.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/TaylorMajorization/Result.result`
- Dependency: [D5/S3/Quantum/Matrix/TaylorMajorization/Pauli](Pauli.md)
