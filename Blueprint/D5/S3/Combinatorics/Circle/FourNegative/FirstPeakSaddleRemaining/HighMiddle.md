# The region b>c+d

## Abstract

Unbounded high-middle choices

**Lemma 1.1 (Interpolate the high-middle margins).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HighMiddle.high_interpolate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HighMiddle.high_interpolate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The h=0 and maximal-h charts and the t=2z boundary provide three families of four exact margins. Their sparse integer polynomials are written in Horner form and verified by ring normalization and nonnegative shifted variables. high_interpolate extends the two h endpoints, and high_arithmetic chooses the integer residue and capacities.

**Lemma 1.2 (All strict saddles with high middle exponent).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HighMiddle.high_middle_choice_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HighMiddle.high_middle_choice_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>b>d>c>=2 and b>c+d, the integer construction becomes a NativeChoice through native_of_selection. The 12 polynomial margins apply to the full unbounded parameter region. Native subsequently converts its fixed-q rectangle to the physical twelve gates; this module does not identify rectangle feasibility with a physical word on its own.

These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HighMiddle.high_interpolate`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HighMiddle.high_middle_choice_exists`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/Arithmetic](Arithmetic.md)
