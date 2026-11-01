# All a>=2, d>=a+1, c>=a+d+1, b>=c+1

## Abstract

Four independent gaps: native ceiling allocation

**Theorem 1.1 (One physical order, two full source rows, literal cut zero).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLargeThirdGap/Endpoint.actualSource_second_peak_large_third_gap_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLargeThirdGap/Endpoint.actualSource_second_peak_large_third_gap_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural a,b,c,d satisfying a>=2, d>=a+1, c>=a+d+1 and b>=c+1, put k=a+b+c+d and A=1+2^a+2^(a+b)+2^(a+b+c). The endpoint has exactly these four data binders and four original proof binders. A single list sigma permutes every distinct physical Fin k label. Inserting the one fresh Fin.last k label at the one literal cut zero gives the enlarged word. Both OriginalOrder readouts retain their exact zero totals and bounds for every natural take-prefix, including empty, full and overlong prefixes. The unrestricted b-maximum joint lift and Circle J/C3.1 remain open.

The ordinary ceiling construction and complete coefficient maps come from the supplied uniform_selector_proof.txt, uniform_selector.py and uniform_selector_certificate.json. The formal source reuses PacketNormalForm.Source for actual chain values, signs, base bounds and totals, FirstPeakSecondMaximum.Native for doubled terminal identities, Chambers.Masks for weighted physical decoding, and the existing four_strip and physical lift lemmas for all prefixes. The exact cited repository snapshot is 4b62d1ff02a702a51332eae3324db7daac400cd5.

Write x=2^a, t=2^d, z=2^c, y=2^b, N=xyzt-1 and Q=2N+1. The four chains U,V,W,X have physical offsets 0,d,d+c,d+c+b and lengths d,c,b,a. Set D=y(z+1)+1, A=xD+1, B=xt(y+1)+t+1, L=xzt+zt+z+1 and M=tyz+D. Their new heads are 2A, Bn=2B-1, Ln=2L-z-1 and Mn=2M-D. The cyclic relation is dynamic in all four parameters: tA=N+B, zB=N+L, yL=N+M and xM=N+A, with new relations 2tA=Q+Bn, zBn=Q+Ln, yLn=Q+Mn and xMn=Q+A. The positive occurrences are the native dyadic ladders; the terminals have doubled values successor minus modulus. The fresh source value is exactly A.

The independent unbounded parameters are x>=4, R=2^(d-a-1)>=1, Z=2^(c-a-d-1)>=1 and lambda=2^(b-c-1)>=1. They satisfy t=2xR, z=2xtZ and y=2zlambda. Define E=2N-M-(t-1)A and H=ceil(E/(2lambdaL)) using the signed integer expression -floor(-E/(2lambdaL)). Euclidean remainder proves delta=2lambdaLH-E lies in [0,2lambdaL). The exact gates E>=0 and E<=2lambdaL(z-1) prove 0<=H<=z-1 before converting H to a natural mask.

Let h=lambdaH, m=(z-1)lambda and low=lambda-1. Uniqueness of sums of distinct powers of two identifies multiplication by lambda as the literal shift of a native bit support. Thus h is a submask of the contiguous c-bit block m. The xor mask m XOR h is its actual complement, not an interchangeable numeric charge. These two supports are disjoint; low is disjoint from both; their union is all b-1 W-positive indices. Their weighted sums are hL, (m-h)L and low L, and similarly with Ln. The physical banks are all U positives followed by terminal W; W mask h followed by terminal X; W mask m XOR h and all X positives followed by terminal U; and all V positives and W mask low followed by terminal V.

Actual paired inventory sums give doubled old seams B+M-2A, delta, 2(B-lambdaL),0 and doubled new seams 2B-2A+Mn-1, 2delta+A-D-2h(z+1)-2, 2(Bn-lambdaLn),0. The respective terminal successors are M,A,B,L in the old row and Mn,A,Bn,Ln in the new row. Define K=L(A-D-2)-E(z+1) and J=L(A-1)-2lambdaL Ln-K. The exact rounding identity L times the doubled second new seam equals Ln delta+K. Positivity of L and Ln, K>=0 and J>=0 therefore bound this rounded seam without a continuous relaxation.

All fourteen polynomial gates are explicit ring identities followed by positivity after x=4+u, R=1+v, Z=1+w, lambda=1+q with u,v,w,q>=0. FirstSeams supplies four gates with 498 positive coefficients; CeilingGates supplies E, the H upper bound and the old second cap with 420; RoundingGates supplies K and J with 760; TailGates supplies both third seams, both third caps and N-A with 384. Selection consumes every gate. The coefficient maps are fallible input to source generation; Lean receives ordinary integer expressions and proof terms, never a Python or JSON assertion of equality.

Each bank contains actual nonnegative source occurrences before its one actual negative terminal. A doubled post-terminal seam between zero and successor minus one puts its preceding peak at most (modulus-1)/2. The four-strip argument covers every intermediate prefix; source totals cover the last bank and overlong takes. Gate N-A supplies the actual fresh prefix. Native support partition and interval concatenation supply the full old permutation, and marked_word supplies the literal ear identity. The Reg companion states the entire eight-binder family through two actual OriginalOrder readouts, proves whole-family variation and role deletion plus actual seed dependence, and leaves continuation unknown.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLargeThirdGap/Endpoint.actualSource_second_peak_large_third_gap_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLargeThirdGap/Schedule](Schedule.md)
