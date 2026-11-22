# Density of actual zeta zeros in a fixed right strip

## Abstract

Density of actual zeta zeros in a fixed right strip

**Theorem 1.1 (Sublinear dyadic zero count by a power).**

Lean statement: `D5/S3/Weil/RightStripZeroDensity.rightStripDyadicCount_power_saving`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/RightStripZeroDensity.rightStripDyadicCount_power_saving` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each fixed real σ greater than one half, the multiplicity-weighted number of actual zeta zeros with real part above σ and T < |Im ρ| ≤ 2T is bounded by D T^(1−η), with D ≥ 0 and η > 0 independent of T. The argument proves this quantitative conclusion by a finite Möbius convolution, the actual zeta truncation mean square, and weighted disk overlap.

**Theorem 1.2 (Reciprocal heights are summable with multiplicity).**

Lean statement: `D5/S3/Weil/RightStripZeroDensity.summable_rightStrip_inverse_height`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/RightStripZeroDensity.summable_rightStrip_inverse_height` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reciprocal absolute ordinates of the same zeros are summable with their analytic multiplicities. This supplies the finite total support lengths for compact positive filters built from the high zeros in a fixed right strip.

## References

- Truth anchor: `D5/S3/Weil/RightStripZeroDensity.rightStripDyadicCount_power_saving`
- Truth anchor: `D5/S3/Weil/RightStripZeroDensity.summable_rightStrip_inverse_height`
- Dependency: [D5/S3/Weil/MollifiedDyadicMeanSquare](MollifiedDyadicMeanSquare.md)
- Dependency: [D5/S3/Weil/RightStripInverseHeight](RightStripInverseHeight.md)
