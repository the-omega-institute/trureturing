# The complete middle-minimum chamber

## Abstract

A physical floor-mask joint order for strictly ordered middle-minimum gaps

**Theorem 1.1 (One complete physical permutation and one literal ear cut).**

Lean statement: `D5/S3/Combinatorics/Circle/MiddleGap/ThreeNegativeMiddleGapJointLift.actualSource_three_negative_middle_gap_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/MiddleGap/ThreeNegativeMiddleGapJointLift.actualSource_three_negative_middle_gap_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural a,b,c with 2<=b<a<c, put k=a+b+c and u=1+2^a+2^(a+b). The theorem constructs one list sigma of Fin(k) and a natural j<=k such that OriginalOrder(k,u,sigma) and OriginalOrder(k+1,2u,earWord(k,sigma,j)). Each OriginalOrder includes the complete permutation of all physical labels, integer total zero, and both half-modulus bounds on every natural take-prefix, including empty and overlong prefixes. The old labels retain their original identity through castSucc, and the single fresh label k is inserted at the literal cut j.

Write r=2^a, s=2^b, t=2^c, N=rst-1 and C=(N-1)/2. The old actual source is f(i)=center_N(2^i*u), and the new source is g(i)=center_(2N+1)(2^(i+1)*u). The positive physical labels are U_i=i for i<c-1, V_i=c+i for i<b-1 and W_i=c+b+i for i<a-1. The three negative labels are alpha=c-1, beta=c+b-1 and gamma=k-1. Choose m=floor(C/u). The set P is exactly the U-chain binary mask m, T is exactly the W-chain binary mask r/2-1, and Q is the literal complement of P,T and the three negative labels in range(k). The word is [P,beta,Q,alpha,T,gamma], and j=|P|+1. The bound m<t/2 follows from C<u*t/2, so P fits its chain. The T mask fits its own chain, which is disjoint from P. The existing physical-inventory lemma proves exhaustiveness and no repeated physical labels. Any fixed internal ordering of each positive block works.

Put B=1+t+tr and L=1+s+st. The paired positive values are U_i=(u*2^i,2u*2^i), V_i=(B*2^i,(2B-1)*2^i) and W_i=(L*2^i,(2L-s-1)*2^i). The old negative magnitudes are H_alpha=(N-B)/2, H_beta=(N-L)/2 and H_gamma=(N-u)/2. The new magnitudes are K_alpha=2H_alpha+1, K_beta=2H_beta+s/2+1 and K_gamma=2H_gamma+(u+1)/2. These identities use the public actual_source_chains theorem at (a,b,c) and at (a,b,c+1), both at the same original seed, followed by the literal index+1 identity. The fresh source g(k)=u follows from centered_full_period. No cyclic relabelling, independent new order or shorter numerical period is used.

The new arithmetic step controls G=C-u*floor(C/u). Set A=st+s/2-1-2G. Since c>a, either t>=4r or t=2r. In the former case G<=u-1 gives A>=2r(s-1)+s/2-1>0. In the latter case write r=h(s+1)+d with 1<=d<=s. The residue d is nonzero because the odd integer s+1>1 is coprime to every power of two. Exact expansion gives C=u(r-h-1)+r(s-d)+h. Its remainder r(s-d)+h is nonnegative and strictly less than rs, since h<r and d>=1. Therefore G<rs and A>s/2-1>0. This estimate is the live floor-remainder inference used by the joint constructor, rather than a feasibility assumption.

The mask sums are x=f(P)=um=C-G, g(P)=2x, y=f(T)=(r/2-1)L and g(T)=(r/2-1)(2L-s-1). Thus g(P)-K_beta=A>0. With delta=H_gamma-y=s(t-r)+s-r and D=K_gamma-g(T), one has delta>=0, D=2delta+r(s+1)-s>=0 and N-K_alpha-D=t(r+1-2s)+r(s+1)-s>0. The conditions r>=2s, s>=4 and t>=2r establish the signs. The first new seam implies H_beta<=x<=C; the tail slack implies y<=H_gamma and H_alpha+H_gamma-y<=C. These are the exact old seams. For the new word the fresh positive u begins Q, and the new seams are K_beta<=g(P)<=N and g(T)<=K_gamma with K_alpha+K_gamma-g(T)<=N.

The reused source_zero theorem establishes both complete actual integer totals. The complete physical inventory and these totals identify the middle block endpoint from the tail mass. The reused physical_schedule strip proof controls every interior positive prefix and both endpoints of each negative step. The reused lift_order and marked_word lemmas transfer this complete natural-label schedule to Fin(k) and to the literal earWord at j. All these helper applications are consumed in the final proof. The floor-mask remainder estimate and its connection to this simultaneous physical order supply the new mathematical inference.

This proves the entire strict chamber 2<=b<a<c of the joint-order problem associated with Circle Conjecture 3.1 of Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2. The construction follows the supplied independently approved ordinary floor-mask proof. The equal-outer and minimum-two statements are not prerequisites for this chamber: only general source, inventory, strip and ear machinery is reused. Full C3.1 remains active and open.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/MiddleGap/ThreeNegativeMiddleGapJointLift.actualSource_three_negative_middle_gap_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/ThreeBitSource](../ThreeBitSource.md)
- Dependency: [D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterJointLift](../ThreeNegativeEqualOuterJointLift.md)
