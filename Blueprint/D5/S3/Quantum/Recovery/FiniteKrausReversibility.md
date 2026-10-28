# FiniteKrausReversibility

## Abstract

Scalar error products construct a normalized finite Kraus left inverse. Spectral zero weights are eliminated explicitly. The reverse implication and canonical channel interface are treated in neighboring modules.

The complementary-channel formulation is the exact identity-target specialization of the recovery duality theorem of Beny and Oreshkov; see `D5/L/QuantumChannels/beny2010approximate`.

Let an isometric encoding have logical input and a physical output split into retained and environment factors. Taking environment coordinates gives the retained-channel Kraus family. The environment output entry with indices a and b is the trace of the input multiplied by the product of the adjoint of Kraus b with Kraus a. Consequently a constant environment output on every input matrix is equivalent, by nondegeneracy of the trace pairing, to scalar error products.

Constancy on every density input has the same force. A nonzero positive matrix is its trace times a density matrix; a positive matrix with zero trace is zero. Positive matrices span the complex matrix algebra, so equality of complex-linear maps on all density matrices extends to all matrices. This extension applies both to the constant complementary channel and to a recovery composed with the retained channel.

For a nonzero logical interface, scalar_products_construct_left_inverse constructs normalized recovery Kraus operators and restores every logical matrix. Its complement completion acts on the entire retained output space, so the decoder is trace preserving there, including outside the code support. finite_kraus_quantum_channel supplies the canonical completely positive trace-preserving channel. Conversely, krausRepresentation and left_inverse_error_products apply to any canonical recovery channel and force the same scalar products.

The logical interface must be nonzero. With zero-dimensional logical input and one-dimensional retained and environment outputs, the encoding is an isometry and the condition on all logical density inputs is vacuous, while a trace-preserving map from the retained matrix algebra to the zero algebra does not exist. Injectivity of the retained readout alone also does not assert a completely positive recovery.

**Theorem 1.1 (Scalar products construct a left inverse).**

Lean statement: `D5/S3/Quantum/Recovery/FiniteKrausReversibility.scalar_products_construct_left_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/FiniteKrausReversibility.scalar_products_construct_left_inverse` (`✓ std3`). ∎

*Citation.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Commentary.*

Scalar error products construct a normalized finite Kraus left inverse. Spectral zero weights are eliminated explicitly. The reverse implication and canonical channel interface are treated in neighboring modules.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/FiniteKrausReversibility.scalar_products_construct_left_inverse`
- Dependency: [D5/S3/Quantum/Recovery/OrthogonalSyndromeChannel](OrthogonalSyndromeChannel.md)
