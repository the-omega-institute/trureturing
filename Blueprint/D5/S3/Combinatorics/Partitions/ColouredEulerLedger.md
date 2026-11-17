# Finite coloured partitions and integer Euler coefficients

## Abstract

Finite coloured partitions and integer Euler coefficients

For a part size d appearing with multiplicity m, a multiset of m elements of Fin(colors(d)) records colours of indistinguishable occurrences. A sigma type over ordinary partitions and a dependent product over occurring part sizes give an actual finite carrier. Its cardinality is computed independently from the Euler-series definition, including empty colour sets and degree zero.

**Definition 1.1 (ColouredPartition).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredEulerLedger.ColouredPartition`

*Formalization.* `D5/S3/Combinatorics/Partitions/ColouredEulerLedger.ColouredPartition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is a finite sigma of finite products of symmetric powers. Finite cardinality is actual type cardinality, not a symbol assigned to the desired coefficient.

**Theorem 1.2 (coloured coefficient).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredEulerLedger.coloured_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/ColouredEulerLedger.coloured_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fintype cardinality gives the product of multichoose values for every partition. Mathlib identifies this weighted partition generating function with its infinite product. The shared local-factor reconstruction and the actual HasProd theorem of the existing Euler series identify the two coefficient functions.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredEulerLedger.ColouredPartition`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredEulerLedger.coloured_coefficient`
- Dependency: [D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality](../../../S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.md)
- Dependency: [D5/S3/Combinatorics/Partitions/ColouredOddMultiplicity](ColouredOddMultiplicity.md)
