# Extra Antiunitary Partners on a Two-Circulant Stratum

## Abstract

A conjugate-block matrix preserves skew-conjugate orthogonal partners of common-unbiased vectors.

**Theorem 1.1 (The explicit skew-conjugate partner preserves both flatness conditions).**

$$\operatorname{ConjugateBlock}(H, A, B) \land \operatorname{CoordinateUnitAndImageFlat}(H, v, rho) \Rightarrow\\\operatorname{CoordinateUnitAndImageFlat}(H, w, rho) \land \operatorname{Orthogonal}(v, w).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/TwoCirculantExtraAntiunitary.conjugate_block_common_unbiased_orthogonal_partner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For H=[A B; conjugate(B) -conjugate(A)], split a vector v into equal channels vL,vR and define w=(-conjugate(vR),conjugate(vL)). The theorem proves coordinate flatness of w, the same squared-modulus condition for H* w as for H* v, and the exact orthogonality v* w=0.

The proof uses the existing Mathlib block-matrix, matrix-vector product, dot-product, finite-sum, and complex conjugation APIs. The identity H* w=-Theta(H* v) supplies the second flatness condition. Skewness cancels the two channel contributions to v* w.

On the symmetric-block real-parameter stratum of the order-six two-circulant family, this partner can interchange the nontrivial Fourier modes. It is therefore unsafe to infer modewise orthogonality from global orthogonality. The separate rational-interval certificate encloses a concrete counterexample and verifies a twelve-ray induced orthogonality graph. That analytic enclosure and exhaustive completion classification are not conclusions of this Lean declaration.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/TwoCirculantExtraAntiunitary.conjugate_block_common_unbiased_orthogonal_partner`
