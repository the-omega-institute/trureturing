# MUB Completion Scalar Defect

## Abstract

Double completion reduces to flatness, row Grams and two scalar defects.

**Theorem 1.1 (Double completion through two scalar defects).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionScalarDefect.doubleCompletion_iff_oneRelativeGram_twoScalarDefects`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCompletionScalarDefect.doubleCompletion_iff_oneRelativeGram_twoScalarDefects` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a nonempty finite coordinate type, let H be entrywise unit and X and Y be complex Hadamards. A second Hadamard pair X-prime, Y-prime, with X unbiased to X-prime and constant cube cross-Gram equal to the dimension, exists exactly when there is a matrix P with every entry's squared norm equal to the dimension and the following conditions on each of recoverFirst X P and recoverSecond Y P: the sum over all entries of the square of the squared norm minus one is zero, and the matrix times its adjoint is the dimension times the identity.

**Theorem 1.2 (Dimension-six scalar defect criterion).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionScalarDefect.doubleCompletion_iff_oneRelativeGram_twoScalarDefects_six`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCompletionScalarDefect.doubleCompletion_iff_oneRelativeGram_twoScalarDefects_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For H, X and Y of type Mat6 under the same entrywise-unit and Hadamard assumptions, double-completion feasibility is equivalent to a matrix P whose entries have squared norm six. Each recovered factor has zero sum of squared deviations of entry squared norms from one, and its row Gram equals six times the identity. The cube cross-Gram on the completion side has every entry equal to six.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionScalarDefect.doubleCompletion_iff_oneRelativeGram_twoScalarDefects`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionScalarDefect.doubleCompletion_iff_oneRelativeGram_twoScalarDefects_six`
- Dependency: [D5/S3/Quantum/Tomography/MUB/ComplexHadamardEntrywiseDefect](ComplexHadamardEntrywiseDefect.md)
