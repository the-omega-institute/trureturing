# Shifted determinants and one-coordinate trace entropy

## Abstract

An equal-trace shifted determinant identity and the entropy cost of pinching one coordinate.

**Theorem 1.1 (Equal-trace shifted determinant integral).**

Lean statement: `D5/S3/Quantum/Divergence/SingleCoordinatePinchingEntropy.integral_log_det_shift_sub`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/SingleCoordinatePinchingEntropy.integral_log_det_shift_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Péter E. Frenkel (2023). *Integral formula for quantum relative entropy implies data processing inequality*. DOI: [10.22331/q-2023-09-07-1102](https://doi.org/10.22331/q-2023-09-07-1102). URL: <https://arxiv.org/abs/2208.12194>.

*Commentary.*

For finite positive semidefinite complex matrices X and Y on the same coordinate space with equal trace, the difference log det(Y + sI) − log det(X + sI) is integrable on s > 0. Its integral is the real trace of X log X minus the real trace of Y log Y. Zero eigenvalues are allowed.

Sum the scalar shift kernel of UmegakiPencilIntegral in each spectrum with reference b = 1. The log(1 + s) terms cancel by equal dimension. The terms proportional to 1/(1 + s) and their integrated affine corrections cancel by equal trace. The shifted trace-log identity identifies the remaining spectral sums with the log determinants. The unshifted sums are the actual trace pairings by trace_self_cfc.

**Theorem 1.2 (Quantitative one-coordinate pinching bound).**

Lean statement: `D5/S3/Quantum/Divergence/SingleCoordinatePinchingEntropy.trace_entropy_pinching_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/SingleCoordinatePinchingEntropy.trace_entropy_pinching_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The mathlib community (2026). *Schur complements of finite matrices*. URL: <https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/SchurComplement.lean#L369-L373>.

*Acknowledgement.* Péter E. Frenkel (2023). *Integral formula for quantum relative entropy implies data processing inequality*. DOI: [10.22331/q-2023-09-07-1102](https://doi.org/10.22331/q-2023-09-07-1102). URL: <https://arxiv.org/abs/2208.12194>.

*Commentary.*

Let A have retained block F, coupling column h, and last entry a. Let A₀ retain both diagonal blocks and set the two coupling blocks to zero. Suppose u(C ⊕ λ) ≤ A ≤ v(C ⊕ λ) in the Löwner order, where C is positive definite, C ≤ cI, 0 < λ < c, and 0 < d = (v − u)/2 < u. Then the real trace of A log A minus the real trace of A₀ log A₀ lies between zero and [u d²/(u² − d²)] λ [c/(c − λ)] log(c/λ).

The pinching preserves trace. Apply the equal-trace determinant integral and integrate the pointwise Schur bounds. Partial fractions express the upper function as [u d²/(u² − d²)] λ [c/(c − λ)] times the difference 1/(s + uλ) − 1/(s + uc). UniformIntegrals.reciprocal_difference evaluates this last integral to log(c/λ).

In Fibonacci observation entropy, proof.txt §18 gives u = 4/3 and v = 7/3. Then d = 1/2 and u d²/(u² − d²) = 12/55. For c ≥ 3λ, the factor c/(c − λ) is at most 3/2, giving (18/55) λ log(c/λ). Section 20 uses this same estimate for every ladder length L ≥ 4.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/SingleCoordinatePinchingEntropy.integral_log_det_shift_sub`
- Truth anchor: `D5/S3/Quantum/Divergence/SingleCoordinatePinchingEntropy.trace_entropy_pinching_bound`
- Dependency: [D5/S3/Quantum/Divergence/SingleCoordinateSchur](SingleCoordinateSchur.md)
- Dependency: [D5/S3/Quantum/Divergence/UmegakiPencilIntegral](UmegakiPencilIntegral.md)
- Dependency: [D5/S3/Quantum/Divergence/UmegakiRareFlagBKM](UmegakiRareFlagBKM.md)
- Dependency: [D5/S3/Quantum/Subentropy/UniformIntegrals](../Subentropy/UniformIntegrals.md)
