# Every original (a,a,d+2,d), 2<=a and a+2<=d

## Abstract

Third peak plus two: complete original physical construction

**Theorem 1.1 (The original physical joint lift).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualFirstTwoPlusTwo/Endpoint.actualSource_third_peak_equal_first_two_plus_two_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualFirstTwoPlusTwo/Endpoint.actualSource_third_peak_equal_first_two_plus_two_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k=2a+2d+2 and s=1+2^a+2^(2a)+2^(2a+d+2). The construction provides a permutation sigma of every Fin k physical label and j<k with sigma[j]=k-1. The literal earWord has fresh label k at j and the same old terminal k-1 at j+1. Both OriginalOrder(k,s,sigma) and OriginalOrder(k+1,2s,earWord) use the unchanged centered actualSource.

For each scalar separately, every natural take n of every finite repetition m stays in its strip, with m=0, n=0 and overlong takes included. Each repeated complete word has total zero. On old physical labels the new scalar sums to -s, while the fresh label contributes s. These are independent scalar total statements.

With x=2^a and t=2^d, the old heads are A=4tx^2+x^2+x+1, B=tx^2+tx+t+1, L=4t^2x+4t^2+4t+1 and K=4t^2x+4tx+x+1. Polynomial slack certificates cover the high cone x>=8,t>=8x, the boundary t=4x, and x=4,t>=128. Exact integer rounding selects complementary U and V masks; the exceptional a=2,d=4,5,6 constructions retain actual physical inventory.

The physical word has terminal order nV,nW,nX,nU. Its packets are complementary U, all W, all X followed by selected V, and selected U followed by complementary V. In the a=2,d=4 case a specified physical transfer supplies the exceptional windows. Both scalar rows use native physical values and independent zero totals. Nonnegative packet values and terminal windows prove all prefixes, and zero-period transport proves arbitrary finite repetition.

The unrestricted Circle problem remains open. This construction covers exactly the original gap family (a,a,d+2,d) under 2<=a and a+2<=d; no claim of literature novelty is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualFirstTwoPlusTwo/Endpoint.actualSource_third_peak_equal_first_two_plus_two_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakMiddleGap/Endpoint](../SecondPeakMiddleGap/Endpoint.md)
