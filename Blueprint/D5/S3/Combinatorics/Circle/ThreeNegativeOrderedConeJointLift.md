# The complete ordered cone chamber

## Abstract

A physical floor-mask joint order for ordered cone gaps

**Theorem 1.1 (One complete physical permutation and one literal ear cut).**

Lean statement: `D5/S3/Combinatorics/Circle/ThreeNegativeOrderedConeJointLift.actualSource_three_negative_ordered_cone_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ThreeNegativeOrderedConeJointLift.actualSource_three_negative_ordered_cone_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural a,b,c with 2<=a<b<=c, put k=a+b+c and u=1+2^a+2^(a+b). The theorem constructs one list sigma of Fin(k) and a natural j<=k such that OriginalOrder(k,u,sigma) and OriginalOrder(k+1,2u,earWord(k,sigma,j)). Each OriginalOrder includes the complete permutation of all physical labels, integer total zero, and both half-modulus bounds on every natural take-prefix, including empty and overlong prefixes. The old labels retain their original identity through castSucc, and the single fresh label k is inserted at the literal cut j.

Write r=2^a, s=2^b, t=2^c, N=rst-1 and C=(N-1)/2. The old actual source is f(i)=center_N(2^i*u), and the new source is g(i)=center_(2N+1)(2^(i+1)*u). The positive physical labels are U_i=i for i<c-1, V_i=c+i for i<b-1 and W_i=c+b+i for i<a-1. The three negative labels are alpha=c-1, beta=c+b-1 and gamma=k-1. Put q=t/s and p=s/2. The set P is the U-chain mask q(p-1), T is the disjoint mask v on V together with r/2-1 on W, where v=floor((L-u)/B), and Q is the literal complement of P,T and the three negative labels in range(k). The word is [P,alpha,Q,beta,T,gamma], and j=|P|+1 in the Q-ear case or j=k-1 in the T-ear case. The bounds q(p-1)<t/2, v<s/2 and r/2-1<r/2 give valid masks. The physical-inventory lemma proves exhaustiveness and no repeated physical labels.

Put B=1+t+tr and L=1+s+st. The paired positive values are U_i=(u*2^i,2u*2^i), V_i=(B*2^i,(2B-1)*2^i) and W_i=(L*2^i,(2L-s-1)*2^i). The old negative magnitudes are H_alpha=(N-B)/2, H_beta=(N-L)/2 and H_gamma=(N-u)/2. The new magnitudes are K_alpha=2H_alpha+1, K_beta=2H_beta+s/2+1 and K_gamma=2H_gamma+(u+1)/2. These identities use the public actual_source_chains theorem at (a,b,c) and at (a,b,c+1), both at the same original seed, followed by the literal index+1 identity. The fresh source g(k)=u follows from centered_full_period. No cyclic relabelling, independent new order or shorter numerical period is used.

The new arithmetic uses the literal floor v=floor((L-u)/B), so vB<=L-u<B(v+1). The old first seam is x-H_alpha=epsilon with epsilon=B-uq=1+q(s-r-1)>=1, while the tail margin is H_gamma-y>=0 by vB<=L-u. The fresh charge is D=K_gamma-g(T)=2(H_gamma-y)+(u+1)/2+v+(r/2-1)(s+1). The beta charge lambda_beta=st+s/2 satisfies lambda_beta>=u. If D<=lambda_beta the ear is placed at the beginning of Q; otherwise D>lambda_beta>=u and the ear is placed after T. These are the two exact physical seam cases.

The old schedule controls the alpha and beta seams directly, and the ordered schedule lemma handles the full positive interiors. For the new word the exact beta endpoint is D in the Q-ear case and D-u in the T-ear case; the chosen branch makes it nonnegative, while the final gamma endpoint is zero. In the T-ear branch the pre-beta endpoint is twice the old pre-beta endpoint plus v-p; the strict floor-mask bound v<p transfers the old strip upper bound to the doubled strip. No independent order or numerical-period reduction is used.

The reused source_zero theorem establishes both complete actual integer totals. The complete physical inventory and these totals identify the ordered beta endpoint from the total mass. The consumed ordered physical schedule proof controls every interior positive prefix and both endpoints of each negative step. The reused lift_order and marked_word lemmas transfer this complete natural-label schedule to Fin(k) and to the literal earWord at j. All these helper applications are consumed in the final proof. The floor mask and exact charge split supply the new mathematical inference.

This proves the complete ordered cone 2<=a<b<=c of the joint-order problem associated with Circle Conjecture 3.1 of Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2. The construction follows the supplied independently approved ordinary floor-mask proof. The equal-outer and minimum-two statements are not prerequisites: only general source, inventory, strip and ear machinery is reused. Full C3.1 remains active and open.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/ThreeNegativeOrderedConeJointLift.actualSource_three_negative_ordered_cone_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/ThreeBitSource](ThreeBitSource.md)
- Dependency: [D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterJointLift](ThreeNegativeEqualOuterJointLift.md)
