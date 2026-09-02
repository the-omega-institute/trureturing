# Time-Ordered Memory Matrix Representation

## Abstract

The frozen timed memory cocycle is the upper-right entry of a matrix word.

**Definition 1.1 (Memory state column).**

Lean statement: `D5/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation.memoryStateVector`

*Formalization.* `D5/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation.memoryStateVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The memory and scalar coordinates are placed in a two-component complex column vector.

**Definition 1.2 (Timed event matrix).**

Lean statement: `D5/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation.timedEventMatrix`

*Formalization.* `D5/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation.timedEventMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One frozen affine event update is represented by an upper-triangular two-by-two complex matrix.

**Definition 1.3 (Chronological word matrix).**

Lean statement: `D5/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation.timeOrderedWordMatrix`

*Formalization.* `D5/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation.timeOrderedWordMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite word matrix stores the stable power, memory cocycle, zero lower-left entry, and scalar cocycle.

**Definition 1.4 (Reverse-ordered matrix product).**

Lean statement: `D5/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation.chronologicalMatrixProduct`

*Formalization.* `D5/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation.chronologicalMatrixProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The head event acts first, so later event matrices multiply on the left of earlier event matrices.

**Theorem 1.5 (Memory cocycle is the upper-right entry).**

$$\operatorname{timeOrderedWordMatrix}(s, w, 0, 1) = \operatorname{timeOrderedMemoryCocycle}(s, w)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation.time_ordered_word_matrix_upper_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Matrix-vector multiplication reproduces the existing timed affine update exactly, so the closed word matrix acts as the frozen list evolution on every memory/scalar state; a one-event word summary is exactly the corresponding event matrix, and concatenation is represented by the later word matrix multiplied by the earlier word matrix.

The event-by-event matrix product equals the matrix assembled from the existing scalar and memory cocycles, identifying the complete finite memory summary with the upper-right coefficient and the scalar word cocycle with the lower-right coefficient.

Swapping two timed events changes the upper-right coefficient by the already frozen prime swap curvature.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation.chronologicalMatrixProduct`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation.memoryStateVector`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation.timeOrderedWordMatrix`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation.time_ordered_word_matrix_upper_right`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation.timedEventMatrix`
- Dependency: [D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle](TimeOrderedPrimeMemoryCocycle.md)
