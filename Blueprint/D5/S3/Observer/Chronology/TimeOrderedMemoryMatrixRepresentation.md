# Time-Ordered Memory Matrix Representation

## Abstract

Time-ordered affine memory evolution is exactly an upper-triangular matrix representation of chronological words.

**Definition 1.1 (One-event update matrix).**

Lean statement: `D5/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation.timedPrimeUpdateMatrix`

*Formalization.* `D5/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation.timedPrimeUpdateMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A timed event is represented by a two-by-two upper-triangular matrix acting on memory and scalar coordinates.

**Definition 1.2 (Chronological word matrix).**

Lean statement: `D5/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation.timeOrderedMemoryMatrix`

*Formalization.* `D5/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation.timeOrderedMemoryMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix of a word is the reverse ordered product because the head event acts first on a column state.

**Theorem 1.3 (Matrix action equals the affine update).**

Lean statement: `D5/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation.timed_prime_update_matrix_mulVec`

*Formalization.* `D5/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation.timed_prime_update_matrix_mulVec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the encoded state by the event matrix reproduces the frozen timed memory update.

**Theorem 1.4 (Word append is reversed matrix multiplication).**

Lean statement: `D5/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation.time_ordered_memory_matrix_append`

*Formalization.* `D5/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation.time_ordered_memory_matrix_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The earlier word acts first, so concatenation maps to the later matrix multiplied by the earlier matrix.

**Theorem 1.5 (Exact triangular cocycle entries).**

Lean statement: `D5/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation.time_ordered_memory_matrix_entries`

*Formalization.* `D5/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation.time_ordered_memory_matrix_entries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The chronological matrix contains the stable power, memory cocycle, zero lower-left entry, and scalar cocycle.

**Theorem 1.6 (Memory is the upper-right entry).**

Lean statement: `D5/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation.time_ordered_memory_matrix_zero_one`

*Formalization.* `D5/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation.time_ordered_memory_matrix_zero_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen time-ordered memory cocycle is exactly the upper-right matrix coefficient.

**Theorem 1.7 (Word matrix realizes full evolution).**

Lean statement: `D5/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation.time_ordered_memory_matrix_mulVec`

*Formalization.* `D5/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation.time_ordered_memory_matrix_mulVec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete matrix product acts exactly as the frozen chronological affine evolution.

## References

- Truth anchor: `D5/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation.timedPrimeUpdateMatrix`
- Truth anchor: `D5/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation.timeOrderedMemoryMatrix`
- Truth anchor: `D5/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation.timed_prime_update_matrix_mulVec`
- Truth anchor: `D5/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation.time_ordered_memory_matrix_append`
- Truth anchor: `D5/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation.time_ordered_memory_matrix_entries`
- Truth anchor: `D5/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation.time_ordered_memory_matrix_zero_one`
- Truth anchor: `D5/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation.time_ordered_memory_matrix_mulVec`
- Dependency: [D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle](../AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.md)
