# One physical permutation couples two centered paths

## Abstract

Equal outer gaps with a literal fresh-first ear

**Theorem 1.1 (The complete complementary family).**

Lean statement: `D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterFirstEarJointLift.actualSource_three_negative_equal_outer_first_ear_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterFirstEarJointLift.actualSource_three_negative_equal_outer_first_ear_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a,b in Nat with 2<=b<=a, set k=a+b+a and v=1+2^a+2^(a+b). There exists one complete permutation sigma of the physical Fin(k) labels such that OriginalOrder(k,v,sigma) and OriginalOrder(k+1,2v,earWord(k,sigma,0)). Both integer totals vanish. Every natural take-prefix, including the empty prefix and every saturated take, is between zero and the respective integer half-modulus. The new list is literally the fresh label k followed by sigma with every old label castSucc. No rotation, numerical-value quotient, coprimality premise, supplied invariant, or second independently chosen permutation occurs.

Write r=2^a, s=2^b, q=2^(a-b), N=r^2*s-1 and C=(N-1)/2. Put B=1+r+r^2 and L=1+s+sr. The positive physical packets are U_i=i, W_i=a+b+i for i<a-1, and V_i=a+i for i<b-1. The three negative physical labels are alpha=a-1, beta=a+b-1 and gamma=k-1. A mask m on a packet selects precisely the physical positions where the binary expansion of m has a one. Its integer mass is the mask times the packet base. Distinct physical labels remain distinct when their numerical source values coincide.

Multiplication by two acts on cyclic residues at each odd modulus. Centering chooses an integer lift of this action. The actual source chains give rv=N+B, sB=N+L and rL=N+v. At modulus 2N+1 the old physical labels have paired positive values U_i=(v*2^i,2v*2^i), V_i=(B*2^i,(2B-1)*2^i), and W_i=(L*2^i,(2L-s-1)*2^i). Thus the doubled integer lift has nonnegative charge defects 0, 2^i and (s+1)*2^i on these packets. The negative magnitudes are Ha=(N-B)/2, Hb=(N-L)/2, Hg=(N-v)/2 and Ka=2Ha+1, Kb=2Hb+s/2+1, Kg=2Hg+(v+1)/2. The fresh label has actual value v. These are identities at the original physical sources, not an abstract replacement source.

Except for two explicit base words, use sigma=[P,beta,Q,alpha,T,gamma], with Q the physical complement of P and T among positive labels. Let x=o(P), xn=v+n(P), t=o(T), tn=n(T). The eight margins are C-x, x-Hb, N-xn, xn-Kb, Hg-t, Kg-tn, C-(Ha+Hg-t), and N-(Ka+Kg-tn). Integer zero totals identify the old endpoints as x, x-Hb, Ha+Hg-t, Hg-t, Hg, 0; the new endpoints after the initial fresh value v are xn, xn-Kb, Ka+Kg-tn, Kg-tn, Kg, 0. Every positive packet is monotone between its endpoints, and every negative step joins two checked endpoints. Nonnegative margins therefore control every natural prefix of both paths using the same physical permutation.

There are six exhaustive parameter cases. If q=1, P is all V and T is all W; their masks are s/2-1 and r/2-1, and Q is all U. The margins reduce to (v-1)/2, 0, r/2-1, v-r, 0, r^2, (v-1)/2, r. For q=2 and s>=8, put tau=2^(b-3), so s=8tau and r=16tau. The masks of P on (U,V,W) are (2tau-1,tau,4tau), and those of T are (6tau,0,2tau-2). The complementary U masks and the separate high W bit prove disjointness. The eight margins are 3s(2s+3)/8, s(2s-5)/8, 7s/8, s(16s-3)/8, (5s^2+4)/4, (15s^2-3s+4)/4, (s+2)(3s-2)/4 and (s^2+11s-4)/4; all are positive.

For s>=8 and q>=4, put n=floor(3qL/v). Choose P masks (0,s/2-3,3q-1) and T masks (n-1,0,r/2-3q). The identity qL=B+q-1>=v gives n>=1, while L<=v gives n<=3q<=r/2. The two W masks sum to the all-ones mask r/2-1 and are disjoint. The first four margins are q(s^2/2-3)+s/2+3, 3(q-1), q(2s-3)+s/2+2 and q(s^2-2s+3)-2. Set d=3qL-vn and e=(v+1)/2+2d+(s+1)(r/2-3q). Euclidean division gives 0<=d<=v-1<=(B-1)/2. Also 0<=e<=3v-2<=B-1, since r>=4s. The last four margins are d, e, (B-1)/2-d and B-1-e.

For s=4 and q>=8, put z=floor(Hg/v), take P to be all W and T to have U-mask z. In half-power coordinates R=r/2>=16, v=1+10R and Hg=8R^2-5R-1. The floor remainder d=Hg-vz lies in [0,10R], z lies in [0,R-1], and Kg-2vz=1+5R+2d<=4R^2+2R=B-1. These estimates give both tail conditions for this single explicit mask. The first four margins are 3r/2+4, (r-4)/2, r/2+3 and 7r/2-1. The two remaining cases are (a,b)=(3,2), with sigma=[3,5,4,0,6,2,1,7], and (4,2), with sigma=[1,4,3,7,8,9,0,2,6,5]. Their actual source values, permutations, totals and every bounded prefix are checked directly; saturated takes follow from the complete total. Powers of two make these six cases exhaustive.

Fresh-first works on this side because the beta-first schedule leaves room for the initial charge v and simultaneously controls the old and doubled tail defects. The smaller-outer theorem ThreeNegativeEqualOuterJointLift covers 2<=a<b with another ear at cut a+1; that theorem is not a proof of this literal first-ear assertion. The present result reuses ThreeNegativeEqualOuterSourceBridge.actual_source_chains, source_zero and physical_schedule, the physical binary-mask infrastructure of ThreeBitSource, and the label transport of RunFirstEarTransport. It concerns the equal-outer family of the Circle Conjecture 3.1 problem in Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2. Full arbitrary-source Circle C3.1 remains OPEN.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterFirstEarJointLift.actualSource_three_negative_equal_outer_first_ear_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/RunFirstEarTransport](RunFirstEarTransport.md)
- Dependency: [D5/S3/Combinatorics/Circle/ThreeBitSource](ThreeBitSource.md)
- Dependency: [D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterJointLift](ThreeNegativeEqualOuterJointLift.md)
- Dependency: [D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterSourceBridge](ThreeNegativeEqualOuterSourceBridge.md)
