# Mechanical Dyadic Boundary

## Abstract

Lower dyadic slope approximations miss an exact mechanical boundary bit at every precision.

**Theorem 1.1 (Lower approximation and boundary bit).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalDyadicBoundary.dyadic_lower_boundary_mismatch`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalDyadicBoundary.dyadic_lower_boundary_mismatch` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an irrational slope strictly between zero and one, the floor dyadic approximation is nonnegative and falls strictly below the slope by less than one binary unit. At phase one minus the exact slope, the first actual mechanical bit is true, while the first bit at every lower dyadic approximation is false. Increasing finite precision cannot remove this specified boundary mismatch.

## References

- Truth anchor: `D5/S1/Words/Mechanical/MechanicalDyadicBoundary.dyadic_lower_boundary_mismatch`
- Dependency: [D5/S1/Words/Mechanical/MechanicalSlopeSensitivity](MechanicalSlopeSensitivity.md)
