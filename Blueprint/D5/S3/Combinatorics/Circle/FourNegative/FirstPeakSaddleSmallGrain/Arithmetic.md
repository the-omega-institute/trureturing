# Three dyadic ratios and exact fixed exceptions

## Abstract

Direct masks for the low-a c=2 branch

**Lemma 1.1 (Select direct masks and all nineteen margins).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleSmallGrain/Arithmetic.select_chart`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleSmallGrain/Arithmetic.select_chart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>b>d>=3 and a<=d+3, the ratio pairs (K,J) are exactly (1,1),(1,2),(2,1). Shared ModTen.phase_cover chooses the four unbounded phases or d=3. The three fixed t=8 checks remain inline in their respective selector branches, with 19 margins each. All-one-mask and even-s cases preserve the actual submask; no fixed-q, grain-bound or reserve-anchor condition is imposed.

**Lemma 1.2 (Existence in the complete small-c2 branch).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleSmallGrain/Arithmetic.arithmetic_choice_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleSmallGrain/Arithmetic.arithmetic_choice_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

choice_of_margins converts the nineteen exact margins to natural s,r,h,v with capacities, inclusion of r-1 in s-1 and the physical seam inequalities. The twelve phase charts in Certificates plus three inline fixed checks give 15 charts and 285 margins. Native converts the first twelve entries directly to JointChoice. This result covers a<=d+3; QuarterStep supplies the complementary c=2 branch.

These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleSmallGrain/Arithmetic.arithmetic_choice_exists`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleSmallGrain/Arithmetic.select_chart`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/ModTen](../FirstPeakSaddle/ModTen.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleSmallGrain/Certificates](Certificates.md)
