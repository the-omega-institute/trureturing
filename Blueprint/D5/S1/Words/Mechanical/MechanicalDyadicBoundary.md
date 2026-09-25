# Mechanical Dyadic Boundary

## Abstract

Lower dyadic slopes miss an exact boundary bit; upper dyadic slopes eventually preserve every fixed finite mechanical observation.

**Theorem 1.1 (Lower approximation and boundary bit).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalDyadicBoundary.dyadic_lower_boundary_mismatch`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalDyadicBoundary.dyadic_lower_boundary_mismatch` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an irrational slope strictly between zero and one, the floor dyadic approximation is nonnegative and falls strictly below the slope by less than one binary unit. At phase one minus the exact slope, the first actual mechanical bit is true, while the first bit at every lower dyadic approximation is false. Increasing finite precision cannot remove this specified boundary mismatch.

**Theorem 1.2 (Upper approximation preserves a finite observation).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalDyadicBoundary.dyadic_upper_eventually_word_eq`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalDyadicBoundary.dyadic_upper_eventually_word_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real slope, phase, and finite word length, all sufficiently precise upper dyadic approximations have the same actual mechanical bits throughout that word. The precision threshold may depend on the slope, phase, and word length, including at integer-hit phases.

**Theorem 1.3 (Finite words away from integer hits).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalDyadicBoundary.finite_word_stable_off_integer_hits`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalDyadicBoundary.finite_word_stable_off_integer_hits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When no positive-time cumulative floor in a fixed finite prefix lands on an integer, one positive slope radius preserves every cumulative floor and every actual mechanical bit in that prefix. The radius is constructed from the finite set of distances to neighboring integers.

## References

- Truth anchor: `D5/S1/Words/Mechanical/MechanicalDyadicBoundary.dyadic_lower_boundary_mismatch`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalDyadicBoundary.dyadic_upper_eventually_word_eq`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalDyadicBoundary.finite_word_stable_off_integer_hits`
- Dependency: [D5/S1/Words/Mechanical/MechanicalSlopeSensitivity](MechanicalSlopeSensitivity.md)
