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

## Balanced reflection phases in even dimension

For d = 2m with m at least one, every complex unitary matrix U on the original d coordinates is a scalar phase times exactly 2(d - 1) balanced reflection phases. A balanced reflection H is selfadjoint, satisfies H squared equal to the identity, and has m positive and m negative eigenvectors in a unitary eigenbasis. Its phase with real parameter t is the matrix exponential of i t H. The construction below also supplies an actual selfadjoint involution E with E H = -H E for every factor.

Apply D5.S3.QuantumBounds.PeritoTensorBlockBound.unitary_diagonalization directly to U. It gives one unitary P and unit-modulus scalars z_j with P adjoint times U times P diagonal. Set theta_j to Complex.arg(z_j). The pinned argument and exponential identities give abs(theta_j) at most pi and z_j = exp(i theta_j). The columns of this same P are the orthonormal spectral basis; repeated spectral values retain their separate basis coordinates. No simple-spectrum assumption is used.

Fix the last coordinate b and put alpha equal to the average of all theta_j, and beta_i = theta_i - alpha for i different from b. For each such i, choose a bijection from the original d coordinates to two copies of Fin m that sends i to the first copy and b to the second. One obtains such a bijection from the usual finite sum equivalence by two transpositions, so the construction includes m = 1. Assign sign +1 to the first copy and -1 to the second. Interchanging i and b gives a second balanced sign vector. Their difference is twice the difference of the i and b coordinate indicators.

Write D_i and D_i' for the two diagonal sign matrices. Swapping the paired coordinates in the two Fin m copies is an involutive permutation. Its permutation matrix is selfadjoint, squares to the identity and anticommutes with the corresponding diagonal sign matrix. Conjugating both matrices by the same P therefore gives actual matrices H_i, H_i' and their actual companions in the original basis. Both sign sets have cardinality m; unitary conjugation preserves the displayed positive and negative eigenbases.

The centered coefficients sum to zero. Thus theta_j equals alpha plus the sum over i different from b of beta_i times the difference of the i and b indicators, including at j = b. All diagonal sign matrices commute. The diagonal exponential and scalar exponential addition identities now give U = exp(i alpha) I times the ordered product, for each i different from b, of exp(i beta_i H_i / 2) and exp(-i beta_i H_i' / 2). Conjugation of the complete product by P yields an equality of the whole original U. There are d - 1 pairs, hence exactly 2(d - 1) reflection factors, including factors whose parameter is zero.

The triangle inequality bounds abs(alpha) by the average of abs(theta_j), hence by pi. It also gives abs(beta_i / 2) at most pi. Every displayed reflection phase is unitary because its exponent is skewadjoint. These are applications of the existing finite spectral, permutation, cardinality and exponential results, together with normalization of finite sums and products. The argument concerns finite complex matrices and supplies no further ambient CAR realization or physical closure.

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
