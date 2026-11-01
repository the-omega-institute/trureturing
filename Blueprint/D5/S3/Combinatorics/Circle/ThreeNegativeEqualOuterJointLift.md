# A common zero cut for equal outer gaps

## Abstract

A common physical order and a marked ear for equal outer gaps

**Theorem 1.1 (The complete marked joint order).**

Lean statement: `D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterJointLift.actualSource_three_negative_equal_outer_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterJointLift.actualSource_three_negative_equal_outer_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of natural numbers a,b with 2<=a<b, put k=a+b+a and v=1+2^a+2^(a+b). There is one list sigma of Fin(k) physical labels such that OriginalOrder(k,v,sigma) and OriginalOrder(k+1,2v,earWord(k,sigma,a+1)). OriginalOrder includes permutation of all labels, integer total zero, and the closed half-modulus bounds for every natural take-prefix, including empty and saturated takes. The new word retains the identical old physical labels in the identical order and inserts the fresh label k at the literal cut a+1.

Let m=b-a-1, r=2^a, s=2^b=2r*tau, tau=2^m, N=r^2*s-1 and C=(N-1)/2. The positive physical chains are U_i=i for i<a-1, V_i=a+i for i<b-1 and W_i=a+b+i for i<a-1. The negative physical labels are alpha=a-1, beta=a+b-1 and gamma=k-1. Split the V chain into P=(V_m,...,V_(b-2)) and its low complement. Put Q=(W_0,...,W_(a-2)) and T=(U_0,...,U_(a-2),V_0,...,V_(m-1)). Then sigma=[P,gamma,Q,beta,T,alpha]. The block P has length a, so the fresh ear is immediately after gamma. When b=a+1, m=0 and the low V block is empty; the same formula applies.

Write B=r^2+r+1 and L=s(r+1)+1. The paired actual positive values are U_i=(v*2^i,2v*2^i), V_i=(B*2^i,(2B-1)*2^i), and W_i=(L*2^i,(2L-s-1)*2^i). The old negative magnitudes are H_alpha=(N-B)/2, H_beta=(N-L)/2 and H_gamma=(N-v)/2. Their new magnitudes are K_alpha=2H_alpha+1, K_beta=2H_beta+s/2+1 and K_gamma=2H_gamma+(v+1)/2. These tables come from the actual centered source chains. In the enlarged source each old physical index corresponds to the next index in the same-seed chain; the new physical label k has value v by the full-period centered identity.

The exact block sums are o(P)=B(r-1)tau, n(P)=(2B-1)(r-1)tau, o(T)=v(r/2-1)+B(tau-1), and n(T)=2v(r/2-1)+(2B-1)(tau-1). Their margins are C-o(P)=tau-1, n(P)-K_gamma=(r^2-r-1)tau+r/2+1, H_alpha-o(T)=(r^2-r-1)tau+r+1, and N-(K_beta+K_alpha-n(T))=(3r+1)tau-2r-2. All are nonnegative because r>=4 and tau>=1. The remaining old high seam has margin C-(H_beta+H_alpha-o(T))=(2r+1)tau-r-1. The paired positive deficits also give n(P)<=2o(P) and n(T)<=2o(T).

The full actual source cycle has integer total zero. With the complete physical inventory this identifies the old seam after Q as H_beta+H_alpha-o(T), and the new seam after the ear and Q as K_beta+K_alpha-n(T). Every positive block stays between its endpoint heights; each negative step has both endpoints in its strip. For the new word the positive middle block begins with the ear itself, so these endpoint checks include both ear-adjacent prefixes. The recursive strip proof gives all natural prefixes without a finite enumeration.

This is the equal-outer three-negative marked family of the Circle Conjecture 3.1 problem of Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2. It does not assert the full arbitrary-source conjecture or a minimum-width characterization. The explicit uniform construction follows the supplied informal equal-outer proof; its mathematical claims concern these actual centered sources and this literal insertion.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterJointLift.actualSource_three_negative_equal_outer_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/RunFirstEarTransport](RunFirstEarTransport.md)
- Dependency: [D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterSourceBridge](ThreeNegativeEqualOuterSourceBridge.md)
