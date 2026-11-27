# Finite Hermitian sign matrices

## Abstract

Hermitian sign matrices have zero trace and fixed energy.

**Definition 1.1 (Hermitian sign matrix).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignMatrix`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal vanishes. Each upper entry is a complex number with real and imaginary parts in {−3/5, 3/5}, and the lower entries are its conjugates.

**Theorem 1.2 (Deterministic energy of the sign matrix).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignMatrix_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignMatrix_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each off-diagonal entry contributes 18/25 to the squared Frobenius norm. Hermiticity turns the sum of entrywise squared moduli into the real trace of the square.

**Theorem 1.3 (The sign matrix construction under three bounds).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignSample_conditional`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignSample_conditional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sign choices supply Hermiticity, tracelessness and sufficient energy. The remaining hypotheses impose the Schmidt-restricted quadratic bound and positive semidefiniteness of both trace tests.

**Definition 1.4 (Sign scalar).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.signScalar`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.signScalar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the first Boolean for the sign of the real part and the second for the sign of the imaginary part. Set both magnitudes to three fifths.

**Theorem 1.5 (Finite sign matrix apply diag).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignMatrix_apply_diag`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignMatrix_apply_diag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every diagonal entry is zero for every pair of sign assignments.

**Theorem 1.6 (Sign scalar norm sq).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.signScalar_normSq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.signScalar_normSq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each complex sign scalar has squared modulus eighteen twenty-fifths.

**Theorem 1.7 (Finite sign matrix is hermitian).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignMatrix_isHermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignMatrix_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lower triangle is the entrywise conjugate of the upper triangle after swapping the indices, and the diagonal is real.

**Theorem 1.8 (Finite sign matrix offdiag norm sq).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignMatrix_offdiag_normSq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignMatrix_offdiag_normSq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every off-diagonal entry has squared modulus eighteen twenty-fifths.

**Theorem 1.9 (Finite sign matrix trace zero).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignMatrix_trace_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignMatrix_trace_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace vanishes because every diagonal entry is zero.

**Definition 1.10 (Finite sign sample).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignSample`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignSample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluate the finite sign matrix construction on pairs of indices in Fin d. Order them via the standard equivalence with Fin(d squared).

**Theorem 1.11 (Finite sign sample is hermitian).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignSample_isHermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignSample_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every sign sample on the product of two copies of Fin d is Hermitian.

**Theorem 1.12 (Finite sign sample trace zero).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignSample_trace_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignSample_trace_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every sign sample on the product of two copies of Fin d has trace zero.

**Theorem 1.13 (Finite sign sample energy).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignSample_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignSample_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real trace of the square is eighteen twenty-fifths times d squared times d squared minus one, with the last subtraction inside the product factor.

**Theorem 1.14 (Finite sign sample energy lower).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignSample_energy_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignSample_energy_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If d is at least two, the real trace of the square is at least d to the fourth power divided by two.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignMatrix`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignMatrix_apply_diag`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignMatrix_energy`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignMatrix_isHermitian`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignMatrix_offdiag_normSq`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignMatrix_trace_zero`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignSample`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignSample_conditional`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignSample_energy`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignSample_energy_lower`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignSample_isHermitian`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.finiteSignSample_trace_zero`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.signScalar`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices.signScalar_normSq`
- Dependency: [D5/S3/Quantum/Entanglement/EntanglementBreaking/ConditionalConstruction](ConditionalConstruction.md)
