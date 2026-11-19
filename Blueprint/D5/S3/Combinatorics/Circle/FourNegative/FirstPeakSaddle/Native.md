# Exact conversions into the physical interface

## Abstract

Joining six native arithmetic regions

**Lemma 1.1 (Exhaustive strict-saddle choice).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Native.native_choice_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Native.native_choice_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a>b>d>c>=2, construct a JointChoice by six regions: b>c+d; b<=c+d,c>=3 with a<c+d, a=c+d or a>c+d; and b<=c+d,c=2 with a<=d+3 or a>=d+4. HighMiddle, GeneralArithmetic, HalfStep, SmallGrain.Arithmetic and QuarterStep supply the respective choices. There is no upper exponent cutoff or external feasibility hypothesis.

**Lemma 1.2 (Rectangle coordinates agree).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Native.rectangle_agrees`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Native.rectangle_agrees` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The remaining rectangle uses t,z,x,y while the diagonal rectangle uses x,y,z,t, and s=q+r. Its direct H is exactly E+rD-h(z+1). gate_agrees separately identifies the entire Fin12 gate vector. The fixed-q branches use rectangle_to_twelve with z>=4. The direct c=2 branch instead identifies its first twelve Fin19 entries with gate and preserves its own capacities and submask without a grain-bound or anchor assumption.

These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Native.native_choice_exists`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Native.rectangle_agrees`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Structure](Structure.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleDiagonal/GeneralArithmetic](../FirstPeakSaddleDiagonal/GeneralArithmetic.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HalfStep](../FirstPeakSaddleRemaining/HalfStep.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HighMiddle](../FirstPeakSaddleRemaining/HighMiddle.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/QuarterStep](../FirstPeakSaddleRemaining/QuarterStep.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleSmallGrain/Arithmetic](../FirstPeakSaddleSmallGrain/Arithmetic.md)
