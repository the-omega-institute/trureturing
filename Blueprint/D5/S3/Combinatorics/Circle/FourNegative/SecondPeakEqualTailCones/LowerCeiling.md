# Rounding within the W capacity

## Abstract

A safe native ceiling mask

Assume 2<=a, a+1<=s and 2s+1<=b. The natural differences u=2^a-4, v=2^s-2*2^a and w=2^b-2*2^s*2^s are nonnegative, and their safe casts give x=4+u,z=2x+v,y=2z^2+w. Equality b=2s+1 gives w=0, so the polynomial estimates include this boundary without another hypothesis.

The actual mask is C=ceil((M-L)/(2L)), implemented by (M-L+2L-1).toNat/(2L).toNat. Positivity of M-L and L justifies the conversions. Natural quotient-remainder arithmetic gives M-L<=2LC<=M+L-1; the capacity polynomial L(y-3)-M+1>0 then proves C<=F=2^(b-1)-1.

Only F is an all-ones mask. The arbitrary submask C and F XOR C are bounded by the positive W capacity, and F XOR C=F-C both naturally and after casting to integers. These exact bit facts feed the lower physical partition; no upper-cone condition a>=s+1 or adaptive X allocation is imposed.

## References

- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/LowerPolynomial](LowerPolynomial.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/Native](Native.md)
