# Original labels and exact unbounded domain

## Abstract

Complete large-third physical joint lift

**Theorem 1.1 (Complete original physical domain).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakLargeThird/Endpoint.actualSource_third_peak_large_third_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakLargeThird/Endpoint.actualSource_third_peak_large_third_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original natural tuple 2<=b<=a<d and d+3<=c put k=a+b+c+d and A=1+2^a+2^(a+b)+2^(a+b+c). One permutation sigma contains every original Fin k label exactly once. A natural j<=k inserts the single fresh label k through earWord. Both OriginalOrder(k,A,sigma) and OriginalOrder(k+1,2A,earWord(k,sigma,j)) hold.

For every natural m,n, the n-term take of m flattened copies of sigma has actual centered-source sum in [0,modulus(k)/2], and the corresponding take of the same repeated ear word lies in [0,modulus(k+1)/2]. Each repeated row has total zero separately for every m. Empty repetitions, zero takes and overlong takes remain quantified.

The complete three-branch selector is interpreted by PacketNormalForm.actual_nat_joint_iff. Existing zero_period_transport extends the two finite physical orders to all natural repetitions without a new feasibility hypothesis. The full Circle problem and the excluded adjacent c=d+1,c=d+2 faces remain open.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakLargeThird/Endpoint.actualSource_third_peak_large_third_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakMiddleGap/Endpoint](../SecondPeakMiddleGap/Endpoint.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakLargeThird/Selection](Selection.md)
