# Hermitian trace tests

## Abstract

The trace norm is controlled by Hermitian operator contractions without a dimension factor. For a Hermitian matrix the optimal test is attained. For an arbitrary complex matrix the real and imaginary parts of a maximizing unitary give a bound with factor two. Empty coordinate types are included.

**Theorem 1.1 (An attaining Hermitian test).**

Lean statement: `D5/S3/Quantum/Foundation/FiniteHermitianTraceDuality.exists_hermitian_traceNorm_test`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteHermitianTraceDuality.exists_hermitian_traceNorm_test` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite Hermitian complex matrix X there is a Hermitian F of operator norm at most one whose real trace pairing with X equals the trace norm of X. The construction takes the real part of a maximizing unitary; the imaginary part contributes zero.

**Theorem 1.2 (Hermitian dual bound).**

Lean statement: `D5/S3/Quantum/Foundation/FiniteHermitianTraceDuality.hermitian_traceNorm_le_tests`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteHermitianTraceDuality.hermitian_traceNorm_le_tests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A bound m on the real trace pairing with every Hermitian contraction bounds the trace norm of a Hermitian X by m.

**Theorem 1.3 (Complex dual bound).**

Lean statement: `D5/S3/Quantum/Foundation/FiniteHermitianTraceDuality.complex_traceNorm_le_twice_tests`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteHermitianTraceDuality.complex_traceNorm_le_twice_tests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary complex X, a bound m on the modulus of its trace pairing with every Hermitian contraction implies traceNorm(X) at most 2m. Both real and imaginary components of the maximizing unitary are used, so the factor two is retained.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FiniteHermitianTraceDuality.complex_traceNorm_le_twice_tests`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteHermitianTraceDuality.exists_hermitian_traceNorm_test`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteHermitianTraceDuality.hermitian_traceNorm_le_tests`
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](FiniteTraceDistance.md)
