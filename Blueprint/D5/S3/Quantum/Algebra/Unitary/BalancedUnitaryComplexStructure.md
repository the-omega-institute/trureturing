# Balanced Unitary Complex Structure

## Abstract

Balanced relative products give complex structures and Hermitian involutions.

**Definition 1.1 (Relative mixed product).**

Lean statement: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeComplexStructure`

*Formalization.* `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeComplexStructure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite complex square matrices A and B, the relative complex structure is twice A times the adjoint of B.

**Theorem 1.2 (Skew-adjoint relative product).**

Lean statement: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeComplexStructure_is_skewAdjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeComplexStructure_is_skewAdjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If A times the adjoint of B plus B times the adjoint of A is zero, the relative complex structure is skew-adjoint.

**Theorem 1.3 (Right unitarity of the relative product).**

Lean statement: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeComplexStructure_mul_conjTranspose`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeComplexStructure_mul_conjTranspose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If A times its adjoint and the adjoint of B times B both equal half the identity, the relative complex structure times its adjoint is the identity.

**Theorem 1.4 (Left unitarity of the relative product).**

Lean statement: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeComplexStructure_conjTranspose_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeComplexStructure_conjTranspose_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the adjoint of A times A and B times its adjoint both equal half the identity, the adjoint of the relative complex structure times that structure is the identity.

**Theorem 1.5 (Square of a skew-adjoint unitary matrix).**

Lean statement: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.square_eq_neg_one_of_skewAdjoint_unitary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.square_eq_neg_one_of_skewAdjoint_unitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A skew-adjoint complex square matrix whose product with its adjoint is the identity has square equal to minus the identity.

**Theorem 1.6 (Complex structure equation).**

Lean statement: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeComplexStructure_square`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeComplexStructure_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cross cancellation, right half-normalization of A and left half-normalization of B imply that the relative complex structure squares to minus the identity.

**Definition 1.7 (Induced involution matrix).**

Lean statement: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeInvolution`

*Formalization.* `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeInvolution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The relative involution is the relative complex structure multiplied by the complex scalar i.

**Theorem 1.8 (Hermitian induced matrix).**

Lean statement: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeInvolution_isHermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeInvolution_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cross cancellation implies that the relative involution equals its adjoint.

**Theorem 1.9 (Involution equation).**

Lean statement: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeInvolution_square`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeInvolution_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cross cancellation, right half-normalization of A and left half-normalization of B imply that the relative involution squares to the identity.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeComplexStructure`
- Truth anchor: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeComplexStructure_conjTranspose_mul`
- Truth anchor: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeComplexStructure_is_skewAdjoint`
- Truth anchor: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeComplexStructure_mul_conjTranspose`
- Truth anchor: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeComplexStructure_square`
- Truth anchor: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeInvolution`
- Truth anchor: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeInvolution_isHermitian`
- Truth anchor: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.relativeInvolution_square`
- Truth anchor: `D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure.square_eq_neg_one_of_skewAdjoint_unitary`
- Dependency: [D5/S3/Quantum/Algebra/Unitary/BalancedUnitarySum](BalancedUnitarySum.md)
