# Ceiling bounds transfer across both rows

## Abstract

Lower-cone local increments and cumulative seams

The lower allocation rows in chain order U,V,W,X are (u,0,0,0), (0,0,C,E), (0,u,0,0), (0,0,F-C,0), where u=z/2-1 and E=x/2-1. Terminal order remains W,U,X,V. The complement F-C appears only in bank 4. The individual doubled old increments are d1=B+M-2A, d2=A+B-2M+2CL and d3=L-2B+A. The enlarged increments are e1=Bn+Mn-4A, e2=A+Bn-2Mn+2CLn and e3=Ln-2Bn+3A; e3 includes the fresh 2A.

The cumulative doubled seams are D1=d1, D2=2B-A-M+2CL, D3=(2C+1)L-M and E1=e1, E2=2Bn-3A-Mn+2CLn, E3=(2C+1)Ln-Mn. The source recurrences prove both the local identities and their cumulative sums. The final bank makes both fourth seams exactly zero.

The identity M*Ln-Mn*L=Az^2 transfers the ceiling bounds M-L<=2LC<=M+L-1 to the enlarged row. Together with the thirteen positive polynomials it gives all twelve gates, with old/new caps (M-1,Mn-1), (B-1,Bn-1) and (A-1,A-1). The rounding residual M-2CL lies between L-A+1 and L and may be negative; the proof does not assume a positive residual.

## References

- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/LowerCeiling](LowerCeiling.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/Seams](Seams.md)
