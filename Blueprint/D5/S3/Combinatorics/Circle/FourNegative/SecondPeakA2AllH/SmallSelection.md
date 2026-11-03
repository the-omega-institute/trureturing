# All unbounded dyadic h and q for the four small p

## Abstract

All unbounded dyadic h and q for the four small p

**Theorem 1.1 (small q partition).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallSelection.small_q_partition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallSelection.small_q_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed part of all unbounded dyadic h and q for the four small p. The complete module scope and assumptions are stated below.

**Theorem 1.2 (small p allh selection).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallSelection.small_p_allh_selection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallSelection.small_p_allh_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed part of all unbounded dyadic h and q for the four small p. The complete module scope and assumptions are stated below.

For every natural p in {4,8,16,32}, every Q>=1 and every H>=2, small_p_allh_selection produces natural v,m,M and a Bool before with Submask m M, strict m<M, and rowBounds 4 p (2^Q) (2^H) v m M before. In particular, all three old and actual charged new endpoint bounds and the v,M stocks hold simultaneously.

The proof partitions q into q>=64 or the five values 2,4,8,16,32 without bounding Q. The first branch uses the signed-ceiling construction. In the latter, H>=3 uses the affine proof for all integers u>=1, while H=2 uses the finite boundary rows. The source input is the supplied small-p all-h construction. These results are a consumed selector component of the original a=2 all-b>d program; they do not assert a physical Circle permutation or complete the original endpoint.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallSelection.small_p_allh_selection`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallSelection.small_q_partition`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallLargeQ](SmallLargeQ.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallTables](SmallTables.md)
