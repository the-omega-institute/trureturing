# Shifted determinants under one-coordinate pinching

## Abstract

Schur complement bounds for pinching one coordinate.

**Theorem 1.1 (Schur term, determinant ratio and logarithmic deficit).**

Lean statement: `D5/S3/Quantum/Divergence/SingleCoordinateSchur.schur_det_log_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/SingleCoordinateSchur.schur_det_log_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The mathlib community (2026). *Schur complements of finite matrices*. URL: <https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/SchurComplement.lean#L369-L373>.

*Commentary.*

Let A have retained block F, coupling column h and last diagonal entry a. Let A₀ be its pinching and let the reference be C ⊕ λ with C positive definite, λ > 0 and C ≤ cI for c > 0. Assume u(C ⊕ λ) ≤ A ≤ v(C ⊕ λ) in the Löwner order and 0 < d = (v − u)/2 < u. At each shift s ≥ 0, the Schur term q = Re(h†(F + sI)⁻¹h) lies between zero and d²λc/(uc + s). The ratio Re det(A + sI)/Re det(A₀ + sI) equals 1 − q/(a + s). The correction q/(a + s) lies between zero and d²λc/((uc + s)(uλ + s)), which is at most d²/u².

The signed midpoint of the two Löwner differences has diagonal blocks dC and dλ and coupling h. Its Schur complement yields hh† ≤ d²λC. A second block test uses F + sI ≥ (u + s/c)C to bound q. The logarithmic deficit log det(A₀ + sI) − log det(A + sI) lies between zero and d²λc/((uc + s)(uλ + s)(1 − d²/u²)). These are the pointwise estimates in Fibonacci observation entropy, proof.txt §18, lines 1098–1117. Section 20, lines 1259–1275, uses the integrated bound in the ladder comparison.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/SingleCoordinateSchur.schur_det_log_bound`
