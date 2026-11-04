# From fourteen gates to a single integer selector

## Abstract

Exact signed ceiling and all paired seam bounds

For integer x>=4 and R,Z,lambda>=1, use t=2xR, z=2xtZ and y=2zlambda with the Algebra heads A,B,L,M and enlarged heads Bn,Ln,Mn. The module consumes all fourteen gates from FirstSeams, CeilingGates, RoundingGates and TailGates. Its signed ceiling is H=-floor(-E/(2lambdaL)), with E=2N-M-(t-1)A and delta=2lambdaLH-E.

The ceiling-range argument identifies delta with the Euclidean remainder of -E modulo the positive denominator. It proves 0<=H<=z-1 and 0<=delta<2lambdaL before Schedule converts H to a natural mask. The doubled second enlarged seam T=2delta+A-D-2lambdaH(z+1)-2 satisfies L T=Ln delta+K exactly; positivity and the K,J gates give 0<=T<=A-1.

The resulting private SeamBounds record contains both first seam ranges with successors M and Mn, both second seam ranges with successor A, and both third doubled seam ranges with successors B and Bn. It also retains the ceiling range, remainder range, rounding identity and fresh bound A<=N. Schedule applies this complete record to the same four-gap physical source; there is no independent choice of an order for each row.

## References

- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLargeThirdGap/CeilingGates](CeilingGates.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLargeThirdGap/FirstSeams](FirstSeams.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLargeThirdGap/RoundingGates](RoundingGates.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLargeThirdGap/TailGates](TailGates.md)
