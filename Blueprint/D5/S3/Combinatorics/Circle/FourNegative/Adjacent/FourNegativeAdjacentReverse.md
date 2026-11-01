# Physical source and prefix support

## Abstract

The reverse adjacent ratio and its physical boundary

The private symbolic construction handles r=n>=3,s=n+1, z=2^n and q=2^(n-1)>=4. Put N=4z^4-1, A=2z^3+z^2+z+1, B=2z^3+2z^2+2z+1, L=4z^3+4z^2+2z+1 and M=4z^3+2z^2+z+1. The independent FourNegativeAdjacentSource table supplies the old and new values on U_h=h,V_h=n+1+h,W_h=2n+2+h,X_h=3n+2+h. Its new coefficients are 2A,2B-1,2L-1-2z and 2M-1-z-2z^2.

Use the literal old order U[1],X^+,X_-,V[1],W^+,W_-,U[z-2],U_-,V[z-2],V_-. The U and V full positive masks z-1 each split as 1 plus z-2. In each chain the first mask is the original lowest physical position and the remaining mask is the consecutive range of positions 1,...,n-1. The W and X positive chains are complete. Inventory proves a permutation of every old physical label. The fresh physical label k is inserted at cut zero.

The negative order is X,W,U,V. The old seams are z+1,2z^3+2z+2,2z+1,0. The new seams are 2z^2+3z+3,4z^3+6z+4,6z+1,0. The simultaneous Gates inequalities establish the old peaks in [0,N/2] and new peaks in [0,N] for every q>=4. The tight new margin at W is z^2-11z/2-4>0. The inherited four_strip theorem combines these seam and peak bounds with positivity inside each literal block, covering all natural prefixes. Both exact zero totals are taken from the existing source_zero theorem.

The remaining boundary r=2,s=3 uses k=10,A=149 and the exact physical list [0,8,9,3,1,7,6,2,4,5], with cut zero. Its old prefixes are 0,149,442,5,174,472,107,436,9,347,0. Its new prefixes are 0,149,447,996,47,384,980,231,880,25,699,0. Kernel reduction checks the full OriginalOrder endpoints, including the physical permutation, exact totals and every natural prefix. This single boundary completes the symbolic reverse-ratio branch; it is not evidence for unbounded parameters.

The private reverse endpoint is consumed by FourNegativeAdjacentNearJointLift. Nonunit seeds and repeated numerical values remain in scope. The far-ratio branches and unrestricted physical J are not proved here.

## References

- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentSource](FourNegativeAdjacentSource.md)
