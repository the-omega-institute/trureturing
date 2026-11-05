# Operator-Norm Leakage of Finite Unitary Averages

## Abstract

Construct the averaging operation and derive quantitative commutator bounds using the C-star norm. A separate Weyl/partial-trace identification is required for the full physical leakage theorem.

**Theorem 1.1 (conjugate norm).**

Lean statement: `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.conjugate_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.conjugate_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The linked Lean source gives the exact hypotheses and conclusion. This is a source candidate; no kernel verification is claimed.

**Theorem 1.2 (conjugation defect norm).**

Lean statement: `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.conjugation_defect_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.conjugation_defect_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The linked Lean source gives the exact hypotheses and conclusion. This is a source candidate; no kernel verification is claimed.

**Theorem 1.3 (average norm le).**

Lean statement: `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.average_norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.average_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The linked Lean source gives the exact hypotheses and conclusion. This is a source candidate; no kernel verification is claimed.

**Theorem 1.4 (average defect).**

Lean statement: `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.average_defect`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.average_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The linked Lean source gives the exact hypotheses and conclusion. This is a source candidate; no kernel verification is claimed.

**Theorem 1.5 (average defect le leakage).**

Lean statement: `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.average_defect_le_leakage`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.average_defect_le_leakage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The average and maximum are explicitly constructed. Triangle inequality and right-unitary invariance prove that the average defect is bounded by the largest measured commutator. No contraction conclusion is assumed.

**Theorem 1.6 (leakage le twice norm).**

Lean statement: `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.leakage_le_twice_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.leakage_le_twice_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The linked Lean source gives the exact hypotheses and conclusion. This is a source candidate; no kernel verification is claimed.

**Theorem 1.7 (centered leakage bounds).**

Lean statement: `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.centered_leakage_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.centered_leakage_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This specialization has an explicit zero-average hypothesis. It must be discharged by a concrete twirl theorem before being cited for the interaction V of the theory.

**Theorem 1.8 (leakage eq zero iff).**

Lean statement: `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.leakage_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.leakage_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The linked Lean source gives the exact hypotheses and conclusion. This is a source candidate; no kernel verification is claimed.

**Theorem 1.9 (sum isometry defect sq).**

Lean statement: `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.sum_isometry_defect_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.sum_isometry_defect_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite-sum polarization gives the exact Hilbert-space square identity. Identification of conjugation as a Hilbert-Schmidt isometry and all dimension normalizations remain separate.

## References

- Truth anchor: `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.average_defect`
- Truth anchor: `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.average_defect_le_leakage`
- Truth anchor: `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.average_norm_le`
- Truth anchor: `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.centered_leakage_bounds`
- Truth anchor: `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.conjugate_norm`
- Truth anchor: `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.conjugation_defect_norm`
- Truth anchor: `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.leakage_eq_zero_iff`
- Truth anchor: `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.leakage_le_twice_norm`
- Truth anchor: `D5/S3/Quantum/Thermal/UnitaryAverageLeakage.sum_isometry_defect_sq`
