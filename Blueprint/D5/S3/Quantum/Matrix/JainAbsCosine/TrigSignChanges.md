# Cosine bases and coefficient signs

## Abstract

Trigonometric coefficients of absolute cosine Fourier modes.

**Theorem 1.1 (Positive bases below one).**

Lean statement: `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.cosine_base_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.cosine_base_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural m and l with 1 at most l at most m, the cosine of l times pi divided by 2m+1 lies strictly between zero and one.

**Theorem 1.2 (Strictly decreasing bases).**

Lean statement: `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.cosine_base_strictAnti`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.cosine_base_strictAnti` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 1 at most a less than b at most m, the cosine base at b is strictly smaller than the base at a. The sample angles lie between zero and pi/2, where cosine is strictly decreasing.

**Theorem 1.3 (Ordered logarithmic exponents).**

Lean statement: `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.logarithmic_exponent_order`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.logarithmic_exponent_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 1 at most a less than b at most m, the logarithm of the base at b is strictly smaller than the logarithm of the base at a, and the latter is strictly negative. These are the exponents of the real exponential sum representation.

**Theorem 1.4 (The sine product expression for a mode gap).**

Lean statement: `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.modeValue_sub`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.modeValue_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m, j and d and every real r, the difference of modes j and j+d equals four times the sum, for l from one to m, of sin((2j+d)l theta) sin(dl theta) cos(l theta) raised to r. Here theta is pi/(2m+1). This follows from the difference of two cosines.

**Theorem 1.5 (Positivity of the short sine factor).**

Lean statement: `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.gap_short_sine_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.gap_short_sine_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When d is one or two and 1 at most l at most m, sin(dl theta) is strictly positive. Thus this factor does not alter the sign of a gap coefficient.

**Theorem 1.6 (Exactly j changes in mode coefficients).**

Lean statement: `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.mode_coefficients_signVariations`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.mode_coefficients_signVariations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 1 at most j at most m, the ordered list consisting of one followed by 2cos(2jl theta), for l from one through m, has exactly j sign variations. The order agrees with the strictly decreasing exponents zero, log cos(theta), through log cos(m theta).

**Theorem 1.7 (The first gap phase).**

Lean statement: `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.gap_first_phase_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.gap_first_phase_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 1 at most j, d equal to one or two, and j+d at most m, the phase (2j+d)theta lies strictly between zero and pi. Its sine is therefore strictly positive, which determines the sign of the leading gap coefficient.

**Theorem 1.8 (Exactly j changes in short-gap coefficients).**

Lean statement: `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.gap_coefficients_signVariations`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.gap_coefficients_signVariations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If 1 at most j, d is one or two, and j+d at most m, the ordered list sin((2j+d)l theta) sin(dl theta), for l from one through m, has exactly j sign variations after zero entries are removed. A general arithmetic sampling argument labels nonzero samples by their open sine sign interval. Every interval from zero through j is represented, labels are nondecreasing, and consecutive interval labels have opposite signs. This includes composite odd orders and zero coefficients without a coprimality assumption.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.cosine_base_bounds`
- Truth anchor: `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.cosine_base_strictAnti`
- Truth anchor: `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.gap_coefficients_signVariations`
- Truth anchor: `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.gap_first_phase_bounds`
- Truth anchor: `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.gap_short_sine_pos`
- Truth anchor: `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.logarithmic_exponent_order`
- Truth anchor: `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.modeValue_sub`
- Truth anchor: `D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.mode_coefficients_signVariations`
- Dependency: [D5/S3/Quantum/Matrix/JainAbsCosine/Defs](Defs.md)
