# Refutation of unrestricted Hermitian Taylor majorization.

## Abstract

Refutation of unrestricted Hermitian Taylor majorization.

**Theorem 1.1 (The spectral comparison is false).**

Lean statement: `D5/S3/Quantum/Matrix/TaylorMajorization/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TaylorMajorization/Result.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The claim for all Hermitian matrices and every order at least five is false. Use dimension two, A=Z-I, B=X and order five. Both matrices are Hermitian. Weak majorization would imply the real trace inequality by the full initial sum. The shifted Pauli family instead gives a strictly negative trace defect, contradicting that inequality. The example concerns Hermitian matrices without a positivity restriction.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/TaylorMajorization/Result.result`
- Dependency: [D5/S3/Quantum/Matrix/TaylorMajorization/Pauli](Pauli.md)
