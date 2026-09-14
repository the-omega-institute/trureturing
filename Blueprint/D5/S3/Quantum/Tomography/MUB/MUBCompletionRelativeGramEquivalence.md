# MUB Completion Relative Gram Equivalence

## Abstract

One flat relative Gram characterizes fixed-edge double completion.

**Definition 1.1 (Entrywise conjugation).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence.entrywiseConj`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence.entrywiseConj` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The transparent abbreviation conjugates every entry of a rectangular complex matrix.

**Definition 1.2 (First recovered factor).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence.recoverFirst`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence.recoverFirst` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For complex square matrices X and P on a finite coordinate type, the first recovered factor is X times P scaled by the inverse coordinate cardinality.

**Definition 1.3 (Second recovered factor).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence.recoverSecond`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence.recoverSecond` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For complex square matrices Y and P on a finite coordinate type, the second recovered factor is Y times the entrywise conjugate of P, scaled by the inverse coordinate cardinality.

**Theorem 1.4 (Reconstruction from one relative Gram).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence.oneRelativeGram_reconstructs_doubleCompletion`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence.oneRelativeGram_reconstructs_doubleCompletion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a nonempty finite coordinate type, let H be entrywise unit and X and Y be complex Hadamards. Suppose every entry of P has squared norm equal to the coordinate cardinality and both recovered factors are complex Hadamards. Then X is Hadamard unbiased to the first recovered factor, and the cross-Gram of the original and recovered factorized cube matrices is constant with value equal to the coordinate cardinality.

**Theorem 1.5 (Exact double completion equivalence).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence.doubleCompletion_iff_oneRelativeGram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence.doubleCompletion_iff_oneRelativeGram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a nonempty finite coordinate type, fix entrywise-unit H and complex Hadamards X and Y. Two complex Hadamard factors X-prime and Y-prime exist with X Hadamard unbiased to X-prime and constant cube cross-Gram equal to the coordinate cardinality if and only if there is a matrix P with every squared entry norm equal to that cardinality and both recovered factors complex Hadamard.

**Theorem 1.6 (Dimension-six completion equivalence).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence.doubleCompletion_iff_oneRelativeGram_six`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence.doubleCompletion_iff_oneRelativeGram_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For order-six matrices, with H entrywise unit and X and Y complex Hadamards, the double completion equivalence specializes the constant cube cross-Gram and the squared entry norms of P to six, retaining the same two recovery formulas.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence.doubleCompletion_iff_oneRelativeGram`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence.doubleCompletion_iff_oneRelativeGram_six`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence.entrywiseConj`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence.oneRelativeGram_reconstructs_doubleCompletion`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence.recoverFirst`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence.recoverSecond`
- Dependency: [D5/S3/Quantum/Tomography/MUB/MUBCompletionSingleRelativeGram](MUBCompletionSingleRelativeGram.md)
