# A common four-block schedule and its literal ear cut

## Abstract

Private physical inventory and four-block strip bounds for r=s+1

This module supplies the private Gates predicate and block, four_strip, arithmetic and inventory proofs consumed by FourNegativeAdjacentDoublePhysical. For four nonnegative blocks with masses m1,...,m4 followed by jumps d1,...,d4, put h0=0 and hj=h(j-1)+mj+dj. Gates(C,...) requires C>=0, h1,h2,h3>=0, h4=0 and h(j-1)+mj<=C for j=1,...,4. The block proof bounds each positive block and its following jump; four_strip concatenates these bounds to give InStrip(f,C,0,word), including every natural take-prefix.

Let n=s>=2, r=n+1, k=4n+2, q=2^(n-1) and z=2q. Use N,A,B,L,M and GU,GV,GW,GX from FourNegativeAdjacentDoubleJointLift. Let U=[0,...,n-2], V=[n,...,2n-2], W=[2n,...,3n-1], X=[3n+2,...,4n], x0=3n+1, u=n-1, v=2n-1, w=3n and x=4n+1. The old word is [x0],V,[v],W,[w],U,[u],X,[x]. The inventory proof establishes that it is a permutation of range(k), retaining every physical label once.

The four positive blocks are [x0]++V, W, U and X, followed by jumps at v,w,u,x. Their old masses are M+(q-1)B, (z-1)L, (q-1)A and (z-2)M; their jumps are -(N-L)/2, -(N-M)/2, -(N-B)/2 and -(N-A)/2. The arithmetic proof establishes Gates at capacity N/2, with integer division, for every integer q>=2 and z=2q.

For the new word, insert the fresh physical label k immediately before u. The positive blocks become [x0]++V, W, U++[k] and X. Their masses are GX+(q-1)GV, (z-1)GW, (q-1)GU+A and (z-2)GX; their jumps are -((2N+1)-GW)/2, -((2N+1)-GX)/2, -((2N+1)-GV)/2 and -((2N+1)-A)/2. The same arithmetic proof establishes Gates at capacity N. The number of old labels preceding u is 3n+1=2s+r, so this is the fixed numeric ear cut used by the public endpoint.

The public actualSource_four_negative_adjacent_double_joint_lift proof consumes inventory, arithmetic and four_strip together with the private chain identities. It lifts both natural-label words to physical Fin labels, uses the literal marked-word identity at the stated cut, and uses the existing full-source zero-sum proof to obtain both OriginalOrder conclusions. The result covers r=s+1 with s>=2 only; unrestricted r,s and the full physical J endpoint remain open.

## References

- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentDoubleJointLift](FourNegativeAdjacentDoubleJointLift.md)
