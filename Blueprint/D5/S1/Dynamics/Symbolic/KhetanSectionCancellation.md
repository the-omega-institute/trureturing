# Six-point section cancellation

## Abstract

The 3-by-3 two-point section pattern is incompatible with character cancellation.

The non-product six-point incidence pattern has row pairs 01, 02, and 12. The three corresponding character sums cannot all vanish when the phases have unit modulus. A finite regular-incidence classification identifies this pattern as the only remaining case after the product cases are separated. The finite incidence dichotomy and the resulting regular-case cancellation theorem are recorded separately below.

**Theorem 1.1 (Triangle cancellation obstruction).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.no_triangle_section_cancellation`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.no_triangle_section_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unit-modulus phases cannot have zero sums on all three two-point sections 01, 02, and 12.

**Theorem 1.2 (Regular incidence normal form).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.regular_three_by_three_incidence`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.regular_three_by_three_incidence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every row and every column of a 3-by-3 incidence matrix has two occupied points, the row complements are indexed by a permutation of the three missing columns.

**Definition 1.3 (Count occupied rows in a column).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.columnCount`

*Formalization.* `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.columnCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

columnCount(A,j) is the cardinality of the Fin 3 row set whose section contains column j.

**Theorem 1.4 (Six-point incidence dichotomy).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.six_point_incidence_dichotomy`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.six_point_incidence_dichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A six-point 3-by-3 incidence table with every nonempty row and column containing at least two points is either a two-row product, a two-column product, or has exactly two points in every row and every column. The statement is a finite enumeration and supplies the case split before the character argument.

**Theorem 1.5 (Regular incidence cannot cancel).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.no_regular_three_by_three_section_cancellation`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.no_regular_three_by_three_section_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every row and column has exactly two points, then no unit-modulus phase assignment can make every row section sum to zero. The proof uses the permutation normal form, restores the erased phase with Finset.sum_erase_add, and forces all phases and their total to vanish.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.columnCount`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.no_regular_three_by_three_section_cancellation`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.no_triangle_section_cancellation`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.regular_three_by_three_incidence`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.six_point_incidence_dichotomy`
