# MUB Completion Recovered Row Gram

## Abstract

Recovered completion factors satisfy automatic row-Gram equations.

**Theorem 1.1 (Conjugate preserves the cardinality-square row Gram).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionRecoveredRowGram.entrywiseConj_preserves_cardSq_rowGram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCompletionRecoveredRowGram.entrywiseConj_preserves_cardSq_rowGram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The entrywise conjugate of a matrix whose row Gram is the finite-cardinality square times the identity has the same row Gram.

**Theorem 1.2 (First recovered factor row Gram).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionRecoveredRowGram.recoverFirst_rowGram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCompletionRecoveredRowGram.recoverFirst_rowGram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If X is complex Hadamard and P has the cardinality-square row Gram, the rational recovery of the first factor has the cardinality row Gram.

**Theorem 1.3 (Second recovered factor row Gram).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionRecoveredRowGram.recoverSecond_rowGram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCompletionRecoveredRowGram.recoverSecond_rowGram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If Y is complex Hadamard and P has the cardinality-square row Gram, the conjugate-coupled rational recovery has the cardinality row Gram.

**Theorem 1.4 (Polynomial characterization of double completion).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionRecoveredRowGram.doubleCompletion_iff_scaledRelativeGram_and_twoDefects`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCompletionRecoveredRowGram.doubleCompletion_iff_scaledRelativeGram_and_twoDefects` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For entrywise-unit H and complex Hadamards X and Y, a double completion exists exactly when one relative Gram P has flat entries, the cardinality-square row Gram, and the two recovery defect equations.

**Theorem 1.5 (Dimension-six polynomial specialization).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionRecoveredRowGram.doubleCompletion_iff_scaledRelativeGram_and_twoDefects_six`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCompletionRecoveredRowGram.doubleCompletion_iff_scaledRelativeGram_and_twoDefects_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For order-six matrices, the double-completion equivalence specializes to flat entries of squared norm six, row Gram thirty-six times the identity, and the two recovery defect equations.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionRecoveredRowGram.doubleCompletion_iff_scaledRelativeGram_and_twoDefects`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionRecoveredRowGram.doubleCompletion_iff_scaledRelativeGram_and_twoDefects_six`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionRecoveredRowGram.entrywiseConj_preserves_cardSq_rowGram`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionRecoveredRowGram.recoverFirst_rowGram`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionRecoveredRowGram.recoverSecond_rowGram`
- Dependency: [D5/S3/Quantum/Tomography/MUB/MUBCompletionScalarDefect](MUBCompletionScalarDefect.md)
