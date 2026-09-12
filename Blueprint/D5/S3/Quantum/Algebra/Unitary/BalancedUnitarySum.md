# Balanced Unitary Sum

## Abstract

Balanced unitary summands have cancelling cross terms and a skew-adjoint relative product.

**Definition 1.1 (Half identity normalization).**

Lean statement: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitarySum.halfIdentity`

*Formalization.* `D5/S3/Quantum/Algebra/Unitary/BalancedUnitarySum.halfIdentity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The squared normalization carried by each summand in a balanced unitary sum.

**Theorem 1.2 (Balanced summands have zero mixed Gram sum).**

Lean statement: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitarySum.crossTerms_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Unitary/BalancedUnitarySum.crossTerms_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If S = A + B is unitary and both summands have right Gram matrix I / 2, the mixed Gram terms cancel exactly.

**Theorem 1.3 (The second mixed product is the negative of the first).**

Lean statement: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitarySum.secondCross_eq_neg_first`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Unitary/BalancedUnitarySum.secondCross_eq_neg_first` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cross cancellation says that one mixed product is the negative adjoint of the other.

**Theorem 1.4 (The relative cross product is skew-adjoint).**

Lean statement: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitarySum.crossProduct_is_skewAdjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Unitary/BalancedUnitarySum.crossProduct_is_skewAdjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The relative cross product of a balanced unitary sum is skew-adjoint.

**Theorem 1.5 (Balanced normalization gives the skew-adjoint conclusion).**

Lean statement: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitarySum.crossProduct_is_skewAdjoint_of_balanced_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Unitary/BalancedUnitarySum.crossProduct_is_skewAdjoint_of_balanced_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This direct consumer theorem combines balanced normalization with the skew-adjoint conclusion.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitarySum.crossProduct_is_skewAdjoint`
- Truth anchor: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitarySum.crossProduct_is_skewAdjoint_of_balanced_sum`
- Truth anchor: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitarySum.crossTerms_eq_zero`
- Truth anchor: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitarySum.halfIdentity`
- Truth anchor: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitarySum.secondCross_eq_neg_first`
