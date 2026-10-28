# Finite Unitary Leakage Bounds

## Abstract

An explicit finite average of unitary conjugations is contractive in a C-star norm. Its defect is bounded by the largest tested commutator, with a matching centered lower bound and an exact zero-leakage criterion. A Hilbert-space isometry identity records the corresponding sum of squared defects.

**Theorem 1.1 (Finite average and defect).**

The bundled finite unitary average is explicit, and its conjugation defect is exactly a commutator followed by the adjoint unitary. The average is contractive and its defect is bounded by the maximum commutator leakage.

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.conjugate_norm`, `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.conjugation_defect_norm`, `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.average_norm_le`, `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.average_defect`, and `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.average_defect_le_leakage` (`✓ std3`). ∎

**Theorem 1.2 (Centered leakage sandwich).**

If the finite average of the tested conjugations is zero, the operator norm is at most the maximum commutator leakage, and that leakage is at most twice the operator norm.

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.leakage_le_twice_norm` and `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.centered_leakage_bounds` (`✓ std3`). ∎

**Theorem 1.3 (Zero leakage).**

All tested commutators vanish exactly when the finite leakage is zero.

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.leakage_eq_zero_iff` (`✓ std3`). ∎

**Theorem 1.4 (Isometry square identity).**

For a finite family of real Hilbert-space linear isometries, the sum of squared defects equals the explicit norm/inner-product expression.

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.sum_isometry_defect_sq` (`✓ std3`). ∎

## References

- Truth anchors: the declarations listed in the theorem statements above.
