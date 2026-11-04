# Arithmetic

## Abstract

Third peak second A full cone: Arithmetic

The B second seam separates delta=0 from b=d+1. In the quotient branch delta*x*y=R is an exact power-of-two division, and 4*delta<=q controls the upper gap. The first V seam is L-hB and its enlarged counterpart is S_V-hS_U. Multiplication by 2y gives explicit positive polynomial identities; the upper gap is controlled by z times ((x-2y)t+y(t-1)+t+1)-y. In the A cases b<=d, the second seams are K-HB and S_W-HS_U. When a=d+1, the third seams are A-K-HB and 2A-S_W-HS_U, with enlarged terminal head A. In C, b=d+1 and c=a+1. Writing u=2^(a-d-2)-1 and v=t-4 expresses all six seam lower bounds and all six upper gaps as polynomials with nonnegative coefficients and positive constants. The first C seam is A-MK with M=3*rho/4; its enlarged terminal head is also A.

**Theorem 1.1 (C_seams).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakSecondAFull/Arithmetic.C_seams`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakSecondAFull/Arithmetic.C_seams` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

private theorem C_seams (a b c d : Nat) (hb : 2<=b) (hba : b<a) (hac : a<c) (hd : 2<=d) (hda : d<a) (hbd : b=d+1) (hca : c=a+1) : six exact seam windows

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakSecondAFull/Arithmetic.C_seams`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakSecondAFull/Banks](Banks.md)
