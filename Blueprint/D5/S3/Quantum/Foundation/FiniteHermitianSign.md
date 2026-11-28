# The finite Hermitian sign

## Abstract

The spectral sign of a finite Hermitian matrix vanishes on its kernel and attains its trace norm.

**Definition 1.1 (The Hermitian spectral sign).**

Lean statement: `D5/S3/Quantum/Foundation/FiniteHermitianSign.hermitianSign`

*Formalization.* `D5/S3/Quantum/Foundation/FiniteHermitianSign.hermitianSign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the real sign function to each eigenvalue in an orthonormal spectral basis. The values on strictly positive, zero and strictly negative eigenvalues are 1, 0 and −1.

**Definition 1.2 (The strictly positive spectral subspace).**

Lean statement: `D5/S3/Quantum/Foundation/FiniteHermitianSign.positiveSubspace`

*Formalization.* `D5/S3/Quantum/Foundation/FiniteHermitianSign.positiveSubspace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the complex span of the spectral basis vectors whose eigenvalues are strictly positive.

**Definition 1.3 (The strictly negative spectral subspace).**

Lean statement: `D5/S3/Quantum/Foundation/FiniteHermitianSign.negativeSubspace`

*Formalization.* `D5/S3/Quantum/Foundation/FiniteHermitianSign.negativeSubspace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the complex span of the spectral basis vectors whose eigenvalues are strictly negative.

**Theorem 1.4 (Kernel and extremal eigenspaces of the sign).**

Lean statement: `D5/S3/Quantum/Foundation/FiniteHermitianSign.hermitianSign_eigenspaces`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteHermitianSign.hermitianSign_eigenspaces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sign has the same kernel as the original Hermitian matrix. Its +1 and −1 eigenspaces are the strictly positive and strictly negative spectral subspaces, respectively.

**Theorem 1.5 (The sign attains the trace norm).**

Lean statement: `D5/S3/Quantum/Foundation/FiniteHermitianSign.hermitianSign_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteHermitianSign.hermitianSign_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sign is Hermitian and both I−H and I+H are positive semidefinite for H the sign. Multiplying by the original Hermitian matrix replaces each eigenvalue by its absolute value. The real trace pairing is therefore the trace norm.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FiniteHermitianSign.hermitianSign`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteHermitianSign.hermitianSign_eigenspaces`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteHermitianSign.hermitianSign_spec`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteHermitianSign.negativeSubspace`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteHermitianSign.positiveSubspace`
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](FiniteTraceDistance.md)
