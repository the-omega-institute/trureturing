# Parameters

## Abstract

Third peak second A full cone: Parameters

The source keeps the original four gaps with the exact domain 2<=b<a<c and 2<=d<a. It defines x=2^a, y=2^b, z=2^c, t=2^d, heads A=1+x+xy+xyz, B=1+t+xt+xyt, L=1+z+zt+xzt, K=1+y+yz+yzt, and enlarged heads S_U=2B-1, S_V=2L-z-1, S_W=2K-(1+y+yz). Native bit masks are used throughout. The literal cut is piecewise: 7,8,8 for the three A2 exceptions; a+b+1 in A1/A2 and B1; a+b in B0; and 1 in C.

**Definition 1.1 (freshCut).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakSecondAFull/Parameters.freshCut`

*Formalization.* `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakSecondAFull/Parameters.freshCut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

private def freshCut (a b c d : Nat) : Nat

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakSecondAFull/Parameters.freshCut`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Masks](../MaxPlusTwo/Chambers/Masks.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Endpoint](../PacketNormalForm/Endpoint.md)
