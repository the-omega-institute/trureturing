# Binary masks and the charge of one fresh physical label

## Abstract

A physical joint order when a is smallest and b is largest

**Theorem 1.1 (The complete strict cone, including adjacent gaps).**

Lean statement: `D5/S3/Combinatorics/Circle/ThreeNegativeSmallestALargestBJointLift.actualSource_three_negative_smallest_a_largest_b_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ThreeNegativeSmallestALargestBJointLift.actualSource_three_negative_smallest_a_largest_b_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural a,b,c with 2<=a<c<b, put k=a+b+c and u=1+2^a+2^(a+b). There exist one list sigma of Fin(k) physical labels and a natural j<=k satisfying both OriginalOrder(k,u,sigma) and OriginalOrder(k+1,2u,earWord(k,sigma,j)). Each OriginalOrder includes permutation of all physical labels, complete integer total zero, and every natural take-prefix in the closed strip from zero to half its modulus. The second word literally inserts the fresh label k into sigma, preserving the identity of every old label. There is no unit, distinct-value, primitive-period or bounded-exponent assumption.

Use r=2^a, s=2^b, t=2^c, N=rst-1, C=(N-1)/2, B=1+t+tr, L=1+s+st and u=1+r+rs. The coefficient t is the quantity denoted u in the auxiliary four-case construction, whose seed v is the present u. The actual physical positive ladders are U_i=i, V_i=c+i and W_i=c+b+i, of lengths c-1,b-1,a-1. Their old and embedded-new value pairs are (u*2^i,2u*2^i), (B*2^i,(2B-1)*2^i) and (L*2^i,(2L-s-1)*2^i). The three negative labels are alpha=c-1, beta=c+b-1 and gamma=k-1. Their old magnitudes are H_alpha=(N-B)/2, H_beta=(N-L)/2 and H_gamma=(N-u)/2; their new magnitudes are K_alpha=2H_alpha+1, K_beta=2H_beta+s/2+1 and K_gamma=2H_gamma+(u+1)/2. The physical new index+1 phase supplies these charges and the fresh value u.

A mask triple (x,y,z) means the literal binary support in the U,V,W ladders. The two chosen supports P,T are bounded by their actual ladder capacities and disjoint within each ladder. Q is their physical complement after removing alpha,beta,gamma. In every branch use sigma=[P,beta,Q,gamma,T,alpha] and insert k immediately after beta, so j=|P|+1. The generic realization theorem of ThreeNegativeMinimumTwoJointLift converts these masks and their seam inequalities into both complete physical orders; it is reused without changing its source or restricting its general a,b,c>=2 hypotheses.

When b>=c+2, let d=2^(b-c-2), q=3d and tau=2^(b-a-1). Choose P=(0,s/2-tau,0) and T=(t/2-1,q-1,0). P is the V-tail from index b-a-1 through b-2. The V-support of q-1=3*2^(b-c-2)-1 is strictly below b-a-1: equivalently q-1<tau and P is tau times r-1. The entire U-ladder belongs to T. Hence the supports are disjoint, including b=c+2. With h=2^(a-1) and z=2^(c-a-1), r=2h, t=4hz, s=16hzd; the same masks become P=(0,4zd(2h-1),0), T=(2hz-1,3d-1,0). Their seam margins are polynomial inequalities valid for every h>=2,z>=1,d>=1.

When b=c+1, put z=2^(c-a-1). Choose T=(t/2-r/2,r-2,0). If c<2a, choose P=(z,0,r/2-1); its single U-bit is below the U-tail in T. If c>=2a, choose P=(0,2z,r/2-1); its single V-bit is above the V-support of r-2. Both choices include the whole W-ladder. This switch supplies disjoint physical supports at every ratio, including c=2a. In both branches the same two first-block estimates hold: the larger old mass is at most C and the smaller new mass is at least K_beta. The last-block slack is e=H_alpha-o(T)=t+r(r-1)/2+1>0. Its new margin has twice-value 2(r-2)t-2r^2+r-2, which is positive already at t=2r,r=4 and remains positive throughout the cone.

The four useful inequalities are o(P)<=C, n(P)>=K_beta, o(T)<=H_alpha and n(T)>=K_gamma+K_alpha-N. The formal arithmetic verifies the full eight old/new seam obligations directly. Positive defects give n(P)<=2o(P) and n(T)<=2o(T), while all three negative charges are positive. The old endpoint heights are o(P),o(P)-H_beta,H_gamma+e,e,H_alpha,0. If D=n(P)-K_beta, rho=2o(T)-n(T), and M=n(T)-(K_gamma+K_alpha-N), the new endpoints including the ear are n(P),D,D+u,N-M,2e+rho+1,K_alpha,0. In particular the immediately-after-ear height is D+u=N-M-n(Q)<=N. Monotonicity within every positive block then controls all intermediate natural prefixes. Complete totals use the actual centered-source zero identities, with the same exhaustive physical inventory.

The new mathematical step is the unbounded allocation of literal binary supports with the required simultaneous charge margins, including the adjacent-gap support switch. It is not a new proof of the reused generic physical-realization machinery. This repository construction contributes to the investigation of Conjecture 3.1 of Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2; no literature novelty is asserted. The theorem covers exactly 2<=a<c<b. The full physical joint permutation J and full Circle C3.1 remain open.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/ThreeNegativeSmallestALargestBJointLift.actualSource_three_negative_smallest_a_largest_b_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/ThreeNegativeMinimumTwoJointLift](ThreeNegativeMinimumTwoJointLift.md)
