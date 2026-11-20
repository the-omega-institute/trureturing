# Shared phases for the two c=2 constructions

## Abstract

Exact dyadic phases modulo ten

**Lemma 1.1 (Dyadic phase cover).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/ModTen.phase_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/ModTen.phase_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d>=3, either d=3 or 2^d is 16, 32, 64 or 128 plus ten times a natural number. pow2mod10 proves the four-period residue cycle by induction; the phase proof also establishes the lower bound needed for natural subtraction. The small-c2 selector consumes these alternatives, including its separate d=3 case.

**Lemma 1.2 (Quarter-step phase cover).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/ModTen.quarter_phase_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/ModTen.quarter_phase_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quarter-step version absorbs the 128 phase into 8+10*T, giving the four bases 8,16,32,64. QuarterStep.quarter_arithmetic consumes this cover. These are residue classes for unbounded exponents, not a finite search over exponent values.

These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/ModTen.phase_cover`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/ModTen.quarter_phase_cover`
