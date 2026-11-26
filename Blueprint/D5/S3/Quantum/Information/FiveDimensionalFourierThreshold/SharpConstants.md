# Radicals and exact budget constants

## Abstract

Squared radical identities and rational comparisons certify the deficit and residual coefficients used for the sharp bound.

**Theorem 1.1 (The proposed sharp cutoff).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpConstants.sharpCutoff_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpConstants.sharpCutoff_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact cutoff (14 + 2√5)/5 equals four times the square of the critical singular value c.

**Theorem 1.2 (Joint deficit budget).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpConstants.sharp_budget_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpConstants.sharp_budget_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quantity 2c(1−c) is strictly less than 0.075.

**Theorem 1.3 (Leakage bound).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpConstants.sharp_leakage_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpConstants.sharp_leakage_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A joint spectral deficit below 0.075 bounds leakage by 0.173 when the leakage is charged at the gap c−h.

**Theorem 1.4 (Even-sector margin).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpConstants.sharp_even_margin`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpConstants.sharp_even_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weighted even-sector coefficient plus the mismatch allowance 0.02 is strictly less than 4c.

**Theorem 1.5 (Joint error estimate).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpConstants.sharp_two_errors`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpConstants.sharp_two_errors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two square-root errors are bounded by the square root of the product of their combined weights and budgets.

## References

- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpConstants.sharpCutoff_eq`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpConstants.sharp_budget_lt`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpConstants.sharp_even_margin`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpConstants.sharp_leakage_bound`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpConstants.sharp_two_errors`
- Dependency: [D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveThreshold](FourierFiveThreshold.md)
