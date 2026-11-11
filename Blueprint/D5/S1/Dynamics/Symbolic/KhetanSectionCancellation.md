# Six-point section cancellation

## Abstract

The 3-by-3 two-point section pattern is incompatible with character cancellation.

The non-product six-point incidence pattern has row pairs 01, 02, and 12. The three corresponding character sums cannot all vanish when the phases have unit modulus. A finite regular-incidence classification identifies this pattern as the only remaining case after the product cases are separated.

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

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.no_triangle_section_cancellation`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.regular_three_by_three_incidence`
