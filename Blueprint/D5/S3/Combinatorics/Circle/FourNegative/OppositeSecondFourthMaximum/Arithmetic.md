# Original physical source and both strict sectors

## Abstract

Opposite second/fourth maximum: quotient windows

The quotient-mask construction follows the supplied Pro mathematical construction (SHA256 6895f9bcc25042ab2c2be58543673073aec889bd138a36637a1e4987dd9c7d1e).

Consider the entire strict opposite second/fourth maximum family: natural a,b,c,d with 2<=a, 2<=c, b=d, a<b, c<b and a different from c. Here s=b=d, x=2^a, y=2^s and z=2^c. There is no bound on any exponent or exponent ratio.

The scalar bases are A=1+x+xy+xyz, B=1+y+xy+xy^2, L=1+z+zy+xzy, K=1+y+yz+y^2z; the enlarged bases are 2A, SU=2B-1, SV=2L-z-1 and SW=2K-1-y(z+1). The common window condition for a terminal with head C and residual r is 0<=2r<=C-1.

For a<c, let h=(B-1) div A, m=h-1 and n=(SW-2A) div SV. The three old residuals are B-hA, L-A and K-A-nL; the three enlarged residuals are 2(B-hA)-1, SV-2A and SW-2A-nSV. Euclidean remainders and the oddness of B give the first window. The relation 2(K-A-nL)=e+1+(y-n)(z+1), where e is the third enlarged remainder, gives the old third window. Its headroom slack is K-1-(2L+(y-1)(z+1))=zy(y-2x-2)-z-1.

For c<a, let p=SW div SV, n=p-1 and m=(B-L) div A. The three old residuals are K-pL, A-L and B-L-mA; the enlarged residuals are SW-pSV, 2A-SV and 2(B-L-mA)+z. The first old window uses the exhaustive dyadic alternatives y=2x or 4x<=y. In the second alternative its slack is K-1-(2L+(y-2)(z+1))=yz(y-2x-2). The construction itself uses the same quotient in both alternatives.

Integer quotient bounds are proved with exact emod/ediv identities. The mask capacities 0<=m,n<2^(s-1) follow from 2B<yA and 2SW<ySV, with 2*2^(s-1)=y. The conversion to natural masks keeps the nonnegativity proofs; capacity is proved and is never an endpoint hypothesis. Polynomial positivity uses nonnegative slack variables, including adjacent exponent gaps.

## References

- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakPaidV/Arithmetic](../ThirdPeakPaidV/Arithmetic.md)
