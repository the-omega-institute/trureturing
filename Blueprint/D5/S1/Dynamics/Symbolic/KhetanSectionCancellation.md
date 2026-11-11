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

**Definition 1.3 (Column occupancy count).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.columnCount`

*Formalization.* Repository-derived definition.

*Commentary.*

`columnCount(A,j)` counts the rows whose finite section `A i` contains column `j`.

**Theorem 1.4 (Six-point incidence dichotomy).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.six_point_incidence_dichotomy`

*Formalization status.* The finite-enumeration proof is present in the Lean source; scoped Lean verification is pending for this revision.

*Source.* Repository-derived.

*Commentary.*

A six-point 3-by-3 incidence table whose nonempty rows and columns have at least two points is either a two-row product, a two-column product, or has exactly two points in every row and column.

**Theorem 1.5 (Regular incidence cannot cancel).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.no_regular_three_by_three_section_cancellation`

*Proof.* The proof is present in the Lean source and uses the permutation normal form and `Finset.sum_erase_add`; its current delivery status is pending the scoped Lean verification for this revision.

*Source.* Repository-derived.

*Commentary.*

Under the regular 3-by-3 incidence hypotheses, no unit-modulus phase assignment can make every row section sum to zero. The argument first identifies every phase with the common total, then forces that total, and hence every phase, to vanish.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.no_triangle_section_cancellation`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.regular_three_by_three_incidence`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.columnCount`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.six_point_incidence_dichotomy`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.no_regular_three_by_three_section_cancellation`
