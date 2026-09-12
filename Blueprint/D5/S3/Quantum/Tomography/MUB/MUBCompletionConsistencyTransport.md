# MUB Completion Consistency Transport

## Abstract

Relative-Gram recovery preserves multiplicative transition consistency.

**Theorem 1.1 (Entrywise conjugation preserves matrix multiplication).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistencyTransport.entrywiseConj_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistencyTransport.entrywiseConj_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For complex matrices with a finite shared index type, entrywise conjugation of their product equals the product of their entrywise conjugates in the same order.

**Theorem 1.2 (Entrywise conjugation is involutive).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistencyTransport.entrywiseConj_entrywiseConj`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistencyTransport.entrywiseConj_entrywiseConj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying entrywise complex conjugation twice returns the original matrix, with no finiteness assumption on its index types.

**Theorem 1.3 (Conjugation commutes with inverse-cardinality scaling).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistencyTransport.entrywiseConj_invCard_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistencyTransport.entrywiseConj_invCard_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite type, scaling a complex matrix by the inverse of that type's cardinality commutes with entrywise conjugation.

**Theorem 1.4 (Recovery preserves transition consistency).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistencyTransport.recovery_preserves_transition_consistency`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistencyTransport.recovery_preserves_transition_consistency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H, X, Y and P be complex square matrices on a finite coordinate type and let s be a complex scalar. If H times X equals s times the entrywise conjugate of Y, then H times recoverFirst X P equals s times the entrywise conjugate of recoverSecond Y P.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistencyTransport.entrywiseConj_entrywiseConj`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistencyTransport.entrywiseConj_invCard_smul`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistencyTransport.entrywiseConj_mul`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistencyTransport.recovery_preserves_transition_consistency`
- Dependency: [D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence](MUBCompletionRelativeGramEquivalence.md)
