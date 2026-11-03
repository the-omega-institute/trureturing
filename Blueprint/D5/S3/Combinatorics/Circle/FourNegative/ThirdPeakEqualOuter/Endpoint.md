# Original labels and exact unbounded domain

## Abstract

Complete equal-outer physical face

**Theorem 1.1 (Complete original physical domain).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualOuter/Endpoint.actualSource_third_peak_equal_outer_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualOuter/Endpoint.actualSource_third_peak_equal_outer_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original natural 2<=b<a<c put d=a, k=a+b+c+a and A=1+2^a+2^(a+b)+2^(a+b+c). There exist one permutation sigma of all Fin k labels and j<=k such that the unchanged OriginalOrder(k,A,sigma) and OriginalOrder(k+1,2A,earWord(k,sigma,j)) both hold. The ear inserts exactly the sole fresh label k.

For every natural m,n, the n-term take of m copies of sigma has actual centered-source sum in [0,modulus(k)/2], and that of m copies of the ear word lies in [0,modulus(k)]. For each m, each repeated row has zero total separately. Zero repetitions and zero or overlong takes are included.

The exhaustive physical consumer uses c>=a+3, moderate high, moderate near, small A,small B,small C and the sole local 15-label exception. No extra construction hypothesis is added. The existing zero_period_transport supplies all finite repetitions. The unrestricted Circle objective remains open.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualOuter/Endpoint.actualSource_third_peak_equal_outer_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakMiddleGap/Endpoint](../SecondPeakMiddleGap/Endpoint.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualOuter/ModerateNear](ModerateNear.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualOuter/Small](Small.md)
