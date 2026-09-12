# Complex Hadamard Entrywise Defect

## Abstract

Entrywise unit norms are equivalent to a vanishing squared-deviation sum.

**Theorem 1.1 (Unit entry norms and zero scalar defect).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/ComplexHadamardEntrywiseDefect.entrywiseUnit_iff_sum_normSq_sub_one_sq_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/ComplexHadamardEntrywiseDefect.entrywiseUnit_iff_sum_normSq_sub_one_sq_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a complex matrix with finite row and column types, every entry has squared norm one if and only if the sum over all entries of the square of its squared norm minus one is zero.

**Theorem 1.2 (Hadamard characterization by scalar defect and row Gram).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/ComplexHadamardEntrywiseDefect.isComplexHadamard_iff_scalarDefect_and_rowGram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/ComplexHadamardEntrywiseDefect.isComplexHadamard_iff_scalarDefect_and_rowGram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A complex square matrix on a finite coordinate type with decidable equality is complex Hadamard if and only if its summed squared entry-norm deviations vanish and the matrix times its adjoint equals the coordinate cardinality times the identity.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/MUB/ComplexHadamardEntrywiseDefect.entrywiseUnit_iff_sum_normSq_sub_one_sq_eq_zero`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/ComplexHadamardEntrywiseDefect.isComplexHadamard_iff_scalarDefect_and_rowGram`
- Dependency: [D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence](MUBCompletionRelativeGramEquivalence.md)
