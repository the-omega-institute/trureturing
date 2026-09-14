# MUB Completion Consistent Relative Gram Equivalence

## Abstract

Relative-Gram reduction retains the transition-consistency equation.

**Theorem 1.1 (Relative Gram reduction with transition consistency).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistentRelativeGramEquivalence.consistentDoubleCompletion_iff_oneRelativeGram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistentRelativeGramEquivalence.consistentDoubleCompletion_iff_oneRelativeGram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a nonempty finite coordinate type, let H be entrywise unit and X and Y be complex Hadamards, with H times X equal to a complex scalar s times the entrywise conjugate of Y. A second Hadamard pair X-prime, Y-prime, with X unbiased to X-prime, constant cube cross-Gram equal to the dimension, and the same transition-consistency equation, exists exactly when a matrix P has every entry's squared norm equal to the dimension and both recoverFirst X P and recoverSecond Y P are complex Hadamards.

**Theorem 1.2 (Dimension-six consistent completion).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistentRelativeGramEquivalence.consistentDoubleCompletion_iff_oneRelativeGram_six`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistentRelativeGramEquivalence.consistentDoubleCompletion_iff_oneRelativeGram_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For H, X and Y of type Mat6 under the same entrywise-unit, Hadamard and transition-consistency assumptions, the equivalence retains the equation H times X-prime equals s times the entrywise conjugate of Y-prime. The cube cross-Gram entries and the squared norms of the entries of P are six, and both recovered factors must be complex Hadamards.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistentRelativeGramEquivalence.consistentDoubleCompletion_iff_oneRelativeGram`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistentRelativeGramEquivalence.consistentDoubleCompletion_iff_oneRelativeGram_six`
- Dependency: [D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistencyTransport](MUBCompletionConsistencyTransport.md)
