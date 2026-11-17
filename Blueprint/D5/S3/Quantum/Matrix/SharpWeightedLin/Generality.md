# Hermitian inertia and spectral compression

## Abstract

Hermitian inertia and spectral compression

**Definition 1.1 (Nonnegative inertia count).**

Lean statement: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.nonnegIndex`

*Formalization.* `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.nonnegIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Suvrit Sra (2026). *On Lin's Arithmetic–Geometric Means Conjecture for Singular Values*. URL: <https://suvrit.github.io/papers/linconj/linconj-v1.pdf>.

*Commentary.*

Count all eigenvalues at least zero, including multiplicities.

**Definition 1.2 (Nonpositive inertia count).**

Lean statement: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.nonposIndex`

*Formalization.* `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.nonposIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Suvrit Sra (2026). *On Lin's Arithmetic–Geometric Means Conjecture for Singular Values*. URL: <https://suvrit.github.io/papers/linconj/linconj-v1.pdf>.

*Commentary.*

Count all eigenvalues at most zero, including multiplicities.

**Theorem 1.3 (Positive update inertia identity).**

Lean statement: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.positive_update_inertia`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.positive_update_inertia` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Suvrit Sra (2026). *On Lin's Arithmetic–Geometric Means Conjecture for Singular Values*. URL: <https://suvrit.github.io/papers/linconj/linconj-v1.pdf>.

*Commentary.*

For every invertible finite complex Hermitian H, every rectangular J and every positive definite W, the nonnegative inertia of H + J W J-star equals the positive inertia of H plus the nonpositive inertia of W-inverse + J-star H-inverse J. The rectangular J need not be an isometry. The argument uses both Schur complements of the same Hermitian block matrix, following Sra Lemma 2.1.

**Theorem 1.4 (Nonpositive subspace dimension bound).**

Lean statement: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.finrank_le_nonposIndex`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.finrank_le_nonposIndex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Suvrit Sra (2026). *On Lin's Arithmetic–Geometric Means Conjecture for Singular Values*. URL: <https://suvrit.github.io/papers/linconj/linconj-v1.pdf>.

*Commentary.*

Every complex subspace on which the actual Hermitian quadratic form is nonpositive has dimension at most the nonpositive inertia count. The proof separates it from the range of the positive spectral part.

**Theorem 1.5 (Inverse congruence power bound).**

Lean statement: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.rank_reduction_order`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.rank_reduction_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Suvrit Sra (2026). *On Lin's Arithmetic–Geometric Means Conjecture for Singular Values*. URL: <https://suvrit.github.io/papers/linconj/linconj-v1.pdf>.

*Commentary.*

If E lies below X to the power one over two b, times Y to the power one over a, times the same X power, inverse congruence and the Loewner-Heinz inequality bound the a power of the congruenced E by Y. Here X is positive definite, Y is positive semidefinite, zero is less than a and a is at most one, and b is positive.

**Theorem 1.6 (Inverse support compression formula).**

Lean statement: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.reduced_projection_compression`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.reduced_projection_compression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Suvrit Sra (2026). *On Lin's Arithmetic–Geometric Means Conjecture for Singular Values*. URL: <https://suvrit.github.io/papers/linconj/linconj-v1.pdf>.

*Commentary.*

For positive definite X and a positive semidefinite idempotent E of rank k, the inverse-power congruence of E admits isometric support coordinates J. The compression S of X to the power one over b is positive definite, and the a power of the congruenced projection equals J S to the power minus a J-star, for all positive a and b. The zero rank case is included.

**Theorem 1.7 (Prescribed rank spectral lower projection).**

Lean statement: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.spectral_lower_projection`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.spectral_lower_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Suvrit Sra (2026). *On Lin's Arithmetic–Geometric Means Conjecture for Singular Values*. URL: <https://suvrit.github.io/papers/linconj/linconj-v1.pdf>.

*Commentary.*

If descending eigenvalue j of a finite positive semidefinite matrix is at least one, the first j plus one spectral vectors define a positive semidefinite idempotent E of rank j plus one below that matrix. Indices in Lean start at zero.

**Theorem 1.8 (Inertia threshold gives an indexed spectral bound).**

Lean statement: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.one_le_eigenvalue_of_nonnegIndex_sub_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.one_le_eigenvalue_of_nonnegIndex_sub_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Suvrit Sra (2026). *On Lin's Arithmetic–Geometric Means Conjecture for Singular Values*. URL: <https://suvrit.github.io/papers/linconj/linconj-v1.pdf>.

*Commentary.*

If the nonnegative inertia of A minus the identity is at least j plus one, descending eigenvalue j of the Hermitian A is at least one. This uses the exact correspondence between the sorted spectrum and inertia counts, including zero eigenvalues.

**Theorem 1.9 (Ordered spectrum commutes with positive powers).**

Lean statement: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.eigenvalues_zero_rpow`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.eigenvalues_zero_rpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Suvrit Sra (2026). *On Lin's Arithmetic–Geometric Means Conjecture for Singular Values*. URL: <https://suvrit.github.io/papers/linconj/linconj-v1.pdf>.

*Commentary.*

For a finite positive semidefinite matrix and every nonnegative real exponent, each descending eigenvalue of its continuous functional calculus power is the corresponding descending eigenvalue raised to that exponent.

**Theorem 1.10 (Real scaling of the Hermitian spectrum).**

Lean statement: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.eigenvalues_real_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.eigenvalues_real_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Suvrit Sra (2026). *On Lin's Arithmetic–Geometric Means Conjecture for Singular Values*. URL: <https://suvrit.github.io/papers/linconj/linconj-v1.pdf>.

*Commentary.*

Multiplication by a nonnegative real scalar multiplies each canonical Hermitian eigenvalue by that scalar. The proof reuses the existing descending spectral scaling theorem.

**Theorem 1.11 (Positive scaling preserves nonnegative inertia).**

Lean statement: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.nonnegIndex_real_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.nonnegIndex_real_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Suvrit Sra (2026). *On Lin's Arithmetic–Geometric Means Conjecture for Singular Values*. URL: <https://suvrit.github.io/papers/linconj/linconj-v1.pdf>.

*Commentary.*

Every strictly positive real scalar preserves the full nonnegative inertia count of a finite Hermitian matrix.

**Theorem 1.12 (Matrix order increases nonnegative inertia).**

Lean statement: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.nonnegIndex_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.nonnegIndex_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Suvrit Sra (2026). *On Lin's Arithmetic–Geometric Means Conjecture for Singular Values*. URL: <https://suvrit.github.io/papers/linconj/linconj-v1.pdf>.

*Commentary.*

For finite Hermitian matrices A and B with A below B in the Loewner order, the nonnegative inertia count of A is at most that of B.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.eigenvalues_real_smul`
- Truth anchor: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.eigenvalues_zero_rpow`
- Truth anchor: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.finrank_le_nonposIndex`
- Truth anchor: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.nonnegIndex`
- Truth anchor: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.nonnegIndex_mono`
- Truth anchor: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.nonnegIndex_real_smul`
- Truth anchor: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.nonposIndex`
- Truth anchor: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.one_le_eigenvalue_of_nonnegIndex_sub_one`
- Truth anchor: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.positive_update_inertia`
- Truth anchor: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.rank_reduction_order`
- Truth anchor: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.reduced_projection_compression`
- Truth anchor: `D5/S3/Quantum/Matrix/SharpWeightedLin/Generality.spectral_lower_projection`
- Dependency: [D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound](../LinGProperty/ArithmeticBound.md)
- Dependency: [D5/S3/Quantum/Schatten/SingularValueOrder](../../Schatten/SingularValueOrder.md)
- Dependency: [D5/S3/SpectralTopology/PointGapExactInertia](../../../SpectralTopology/PointGapExactInertia.md)
- Dependency: [D5/S3/Weil/Pick/InvertibleHermitianInertiaPullback](../../../Weil/Pick/InvertibleHermitianInertiaPullback.md)
