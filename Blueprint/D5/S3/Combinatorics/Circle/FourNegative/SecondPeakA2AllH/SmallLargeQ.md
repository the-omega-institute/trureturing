# An unbounded large-q small-p selector

## Abstract

An unbounded large-q small-p selector

**Theorem 1.1 (small ceiling interval).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallLargeQ.small_ceiling_interval`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallLargeQ.small_ceiling_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed part of an unbounded large-q small-p selector. The complete module scope and assumptions are stated below.

**Theorem 1.2 (small large q bounds).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallLargeQ.small_large_q_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallLargeQ.small_large_q_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed part of an unbounded large-q small-p selector. The complete module scope and assumptions are stated below.

**Theorem 1.3 (small large q selection).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallLargeQ.small_large_q_selection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallLargeQ.small_large_q_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed part of an unbounded large-q small-p selector. The complete module scope and assumptions are stated below.

For 4<=p<=32, 4 dividing p, q>=64 and dyadic h=2^H with H>=2, choose m=h/2 and v=pq-p/4. The signed ceiling is the existing ceilDiv from SecondPeakLargeThirdGap.Selection; its bounds reuse signed_ceiling_bounds from SecondPeakParityTail.IntegerSelector. Its negative-input integer semantics are unchanged.

Write c=ceil((y-8hp+4h+5)/(5h)) and M=hc-1. Euclidean ceiling proves c>=2 and 4h<=Delta<9h<=4hp. Put D=5A-8hL, E=8hp^2z-5p(z-1)-1 and R=vA+mL-K. The exact identity 16R=A-D-4E and z>=256, p<=32 give 0<R<A/16. This bounds the first old endpoint 2R and its actual charged enlarged endpoint. The remaining bounds come from SmallWindows. All q and H are unbounded; properness comes from the full h-bit predecessor block.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallLargeQ.small_ceiling_interval`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallLargeQ.small_large_q_bounds`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallLargeQ.small_large_q_selection`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallWindows](SmallWindows.md)
