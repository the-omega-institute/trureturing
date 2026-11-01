# The same physical permutation in both moduli

## Abstract

A literal ear at d in the complete descending four-gap chamber

**Theorem 1.1 (Every independent tuple 2<=d<c<=b<a).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/Descending/Endpoint.actualSource_descending_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/Descending/Endpoint.actualSource_descending_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every four independent natural gaps a,b,c,d with 2<=d<c<=b<a, put k=a+b+c+d and A=1+2^a+2^(a+b)+2^(a+b+c). There exists one permutation sigma of all Fin(k) physical labels satisfying OriginalOrder(k,A,sigma) and OriginalOrder(k+1,2A,earWord(k,sigma,d)). The fresh physical label k is inserted after exactly d entries of this same old permutation. Each order includes the exact complete integer total zero and every natural take-prefix in its half-modulus strip, including empty, full and overlong prefixes. Middle ties b=c, minimum d=2, repeated numerical values and nonprimitive seeds remain in scope. No partition, source formula, feasibility, prefix bound or favorable-cut hypothesis is assumed.

Write x=2^a,y=2^b,z=2^c,t=2^d,N=xyzt-1,D=1+y+yz. The actual old row is centered_N(A*2^i), and the actual new row at old labels is centered_(2N+1)(2A*2^i); the fresh ear has new value A. The accepted packet-source library supplies four chains U,V,W,X of lengths d,c,b,a and offsets 0,d,d+c,d+c+b. Their old positive bases are A=xD+1, B=t(1+x+xy)+1, L=tz(1+x)+1+z, M=tyz+D. Their new bases are 2A, B'=2B-1, L'=2L-1-z, M'=2M-D. Positive local indices run from zero to length minus two; every increment is positive in both rows. The terminal negatives have twice their old values B-N,L-N,M-N,A-N, and twice their new values B'-(2N+1),L'-(2N+1),M'-(2N+1),A-(2N+1). In particular the new X successor is A. These are proved actual centered-source identities, not assumptions.

Put H=a-d-2,E=a-c-1,F=a-b-1. The chamber gives 0<=F<=E<=H and H+2<=a-1. Partition the X positive local positions into bank0={H} union [H+2,a-1), bank1={H+1} union [E,H), bank2=[F,E), bank3=[0,F). Empty intervals are retained; bank2 is empty when b=c. With h=2^H,u=2^E,v=2^F, their dyadic masses are x/2-3h,3h-u,u-v,v-1. Their disjoint physical labels give packets bank0 then X-, all U positives and bank1 then U-, all V positives and bank2 then V-, and all W positives and bank3 then W-. The explicit negative order [X,U,V,W] is proof data; no covariance under arbitrary packet orders is asserted. Bank0 contains exactly d labels, so inserting the ear immediately before X- gives the literal cut d.

The reserve mass telescopes. The three old post-negative seams are S0=A-3hM,S1=B-uM,S2=L-vM; the final seam is zero. The new seams, including the ear, are K0=2A-3hM',K1=B'-uM',K2=L'-vM', again ending at zero. The chain relations tA=N+B,zB=N+L,yL=N+M,xM=N+A and their charged new analogues establish these identities. The dyadic constraints are 4th=x,2zu=x,2yv=x, with t>=4,z>=2t,y>=z,x>=2y and h,u,v>=1. Cleared-denominator identities show S0,S1,S2>=0. The doubled new peak slacks are 6hM'-3A-1,2(uM'-B),2vM'-L'-1. Their nonnegative forms retain only the weaker middle-tie inequalities: the first equals 6h[y(z-2t)+y-2t+1]-4; multiplying the second half by 2z gives xz(y-2t)+2(t+1)(y-z)+y(x-2t-2)+x; multiplying the third by y gives yz(x-2t-1)+y(x-2)+x. Thus the boundary tuple (4,3,3,2) is included.

The other six bounds follow from M'=2M-D. The new seams differ from twice the old seams by 3hD,uD-1,vD-z-1, all nonnegative. Twice each old peak slack minus the corresponding new peak slack is respectively 3hD+(A-1)/2,uD-1,vD-1-z/2, also nonnegative because D>z+1. The last packet peak bounds follow from its negative terminal and the exact zero total. Every positive block rises coordinatewise from the preceding nonnegative seam to its bounded pre-negative peak; its terminal lands at the next seam. The ear adds (0,A). The accepted strip reconstruction therefore proves every prefix in both changing moduli, while labelled permutation reconstruction retains the same old order and cut d.

This is a complete unbounded chamber of physical four-gap J associated with Circle Conjecture 3.1 of Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2. Unrestricted four-gap J remains open, including unaddressed boundary chambers c=d and b=a. This theorem does not replace that goal. No external novelty claim is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/Descending/Endpoint.actualSource_descending_joint_lift`
