# Sorkin Third-Order Cancellation

## Abstract

Quadratic branch weights have no third-order inclusion-exclusion term.

**Definition 1.1 (Quadratic amplitude branch weight).**

Lean statement: `D5/S3/Quantum/SorkinThirdOrder.amplitudeWeight`

*Formalization.* `D5/S3/Quantum/SorkinThirdOrder.amplitudeWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite branch family over a commutative star ring, the weight is the product of the amplitude sum and its star conjugate.

**Theorem 1.2 (Sorkin third-order cancellation).**

Lean statement: `D5/S3/Quantum/SorkinThirdOrder.sorkin_third_order_cancellation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SorkinThirdOrder.sorkin_third_order_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For pairwise disjoint finite branch families A, B and C, the alternating sum of the quadratic weights of A∪B∪C, its three pair unions, and its three singleton unions is zero. The proof is the cancellation of all self and pairwise cross terms after expanding the quadratic amplitude.

## References

- Truth anchor: `D5/S3/Quantum/SorkinThirdOrder.amplitudeWeight`
- Truth anchor: `D5/S3/Quantum/SorkinThirdOrder.sorkin_third_order_cancellation`
