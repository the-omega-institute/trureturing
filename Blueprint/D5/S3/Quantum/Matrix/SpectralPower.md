# Spectral powers and matrix positivity

## Abstract

Real spectral powers and Log-Euclidean means of finite complex matrices, with elementary power identities and a two-dimensional positivity criterion.

**Definition 1.1 (Real matrix powers).**

Lean statement: `D5/S3/Quantum/Matrix/SpectralPower.mpow`

*Formalization.* `D5/S3/Quantum/Matrix/SpectralPower.mpow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite complex square matrix X and real p, mpow X p is cfc (t ↦ t^p) X. On positive definite matrices this is the usual positive real power. The functional calculus is total; this definition alone asserts neither positivity nor Hermitian symmetry for arbitrary inputs.

**Definition 1.2 (Log-Euclidean means).**

Lean statement: `D5/S3/Quantum/Matrix/SpectralPower.LE`

*Formalization.* `D5/S3/Quantum/Matrix/SpectralPower.LE` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

LE α A B is cfc exp ((1−α) • cfc log A + α • cfc log B). For positive definite A and B this is exp((1−α) log A + α log B). The weight α is any real number.

**Theorem 1.3 (The first power).**

Lean statement: `D5/S3/Quantum/Matrix/SpectralPower.mpow_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/SpectralPower.mpow_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Hermitian finite complex matrix X, mpow X 1 = X. This is the identity-function law of the continuous functional calculus.

**Theorem 1.4 (The second power).**

Lean statement: `D5/S3/Quantum/Matrix/SpectralPower.mpow_two`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/SpectralPower.mpow_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Hermitian finite complex matrix X, mpow X 2 = X * X. This follows from the polynomial law of the continuous functional calculus.

**Theorem 1.5 (Positive definite two by two matrices).**

Lean statement: `D5/S3/Quantum/Matrix/SpectralPower.posDef_two`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/SpectralPower.posDef_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real a, b, c, the complex matrix [[a,b],[b,c]] is positive definite if a>0 and ac−b²>0. Its factorization U D U* uses U=[[1,0],[b/a,1]] and D=diag(a,c−b²/a). The diagonal entries are positive and U is invertible. This criterion supplies positivity both for Pauli clock matrices and for Wasserstein counterexamples.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/SpectralPower.LE`
- Truth anchor: `D5/S3/Quantum/Matrix/SpectralPower.mpow`
- Truth anchor: `D5/S3/Quantum/Matrix/SpectralPower.mpow_one`
- Truth anchor: `D5/S3/Quantum/Matrix/SpectralPower.mpow_two`
- Truth anchor: `D5/S3/Quantum/Matrix/SpectralPower.posDef_two`
- Dependency: [D5/S3/Quantum/FiniteDimensional](../FiniteDimensional.md)
