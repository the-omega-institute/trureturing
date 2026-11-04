# One physical order and one literal cut for 2<=a<=b

## Abstract

Complementary two-bank physical joint insertion

**Theorem 1.1 (Unconditional complementary two-negative joint lift).**

Lean statement: `D5/S3/Combinatorics/Circle/TwoNegativeNondecreasingJointLift/Endpoint.actualSource_two_negative_nondec_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/TwoNegativeNondecreasingJointLift/Endpoint.actualSource_two_negative_nondec_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of natural numbers a,b with 2<=a and a<=b, there exist one list sigma permuting all physical labels Fin(a+b) and one natural cut j<=a+b such that OriginalOrder(a+b,2^a+1,sigma) and OriginalOrder(a+b+1,2*(2^a+1),earWord(a+b,sigma,j)). The second word inserts the single fresh label a+b at this literal cut, preserving the relative order of every old physical label. Each OriginalOrder includes exact total zero and every natural take-prefix in the appropriate half-modulus strip, including empty, full and overlong prefixes. No mask, source-identity, feasibility or favorable-cut condition is assumed.

Put k=a+b, q=2^a, r=2^b, Q=2^(a-1), R=2^(b-1), N=qr-1, C=qR-1=(N-1)/2 and w=q+1. Write f(i)=centered_N(2^i*w) and g(i)=centered_(2N+1)(2^i*(2w)). The physical negative labels are alpha=b-1 and beta=k-1. The positive labels are U_i=i for 0<=i<b-1 and V_i=b+i for 0<=i<a-1. Their actual values are f(U_i)=(q+1)2^i, g(U_i)=2(q+1)2^i, f(V_i)=(r+1)2^i and g(V_i)=(2r+1)2^i. The remaining values are f(alpha)=-C+R, f(beta)=-C+Q, g(alpha)=-N+r, g(beta)=-N+Q, and g(k)=w for the fresh label.

These identities hold for all q,r>=4, without comparing a and b. For U_i, 4*2^i<=r implies 2(q+1)2^i<=qr-2; the cleared upper bound is qr-r-4>=0. For V_i, 4*2^i<=q implies 2(r+1)2^i<=qr-2 and (2r+1)2^i<=qr-1; the respective cleared bounds are qr-q-4>=0 and 2qr-q-4>=0. The displayed positive values therefore lie in the centered strips. Their congruences follow by subtracting the old or new modulus once for each V-chain factor 2^i. The alpha congruences subtract one modulus, the beta congruences subtract Q+1 moduli, and the fresh congruence subtracts w moduli. The displayed negative values lie in the strips because q,r>=4. Centered uniqueness identifies every actual value. Summing both complete chains gives exact zero totals in the old row and in the enlarged row including fresh.

For natural masks u<R and v<Q, select the bits of u in the U bank and the bits of v in the V bank. Let E list these selected physical labels in increasing order and let F list the remaining positive labels in a fixed order. The two banks are disjoint and exclude alpha and beta, so sigma=E,alpha,F,beta contains every old label exactly once. Its literal cut is j=length(E); the enlarged word is E,fresh,alpha,F,beta, with every old label mapped by Fin.castSucc. Binary-mask summation gives p=sum_E f=(q+1)u+(r+1)v and z=sum_E g=2(q+1)u+(2r+1)v=2p-v. Thus the V mask is exactly the defect between the new mass and twice the old mass. The two chain directions are (q+1,2q+2) and (r+1,2r+1).

Set h=C-p. It suffices to have 0<=h<=R and q<=2h+v<=q+r. The old pre-alpha and post-alpha heights are C-h and R-h. The enlarged height including fresh is z+w=N+q-2h-v, and the post-alpha height is q+r-2h-v. All entries in E and F, and the fresh entry, are positive. In particular the prefix immediately before fresh is z>=0 and is bounded above by z+w<=N. The old and new pre-beta heights are C-Q and N-Q by the exact total identities; beta returns each to zero. Monotonicity within each positive block and these seam bounds prove every natural prefix. Full and overlong takes have total zero.

If a=b, choose u=Q-1,v=0. Then R=Q, h=Q and 2h+v=q. If b>=a+2, choose u=floor((C-Q)/(q+1)),v=0. The numerator is nonnegative. Euclidean division gives Q<=h<=Q+q, while C-Q<(q+1)R gives u<R. Since R>=2q and r>=4q, h<=R and q<=2h<=3q<=q+r. This single-bank remainder is narrow enough to fit both strips simultaneously. If b=a+1 and a>=3, choose u=1,v=Q-1. Here r=2q,R=q,h=Q-1 and 2h+v=3Q-3. The inequality Q>=4 implies q=2Q<=3Q-3<=q+r, and both masks are in range. These three cases cover every pair except (2,3).

For (a,b)=(2,3), use sigma=[0,1,4,3,2] and j=4. With N=31 and w=5, the old values in this physical order are [5,10,-13,9,-11], with prefixes [0,5,15,2,11,0]. The enlarged values at those same old labels are [10,20,-29,17,-23]. Inserting fresh value 5 at cut 4 gives the full enlarged values [10,20,-29,17,5,-23], with prefixes [0,10,30,1,18,23,0]. These lists are full physical permutations, their totals are zero, and their prefixes lie in [0,15] and [0,31].

This complementary construction covers 2<=a<=b; TwoNegativeJointLift.actualSource_two_negative_joint_lift covers a>b>=2. The two results use actual physical labels and a common literal cut. The complementary construction does not derive its masks by applying the latter theorem. No covariance under cyclic gap permutations, full independent four-gap J, or full Circle C3.1 conclusion follows here.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/TwoNegativeNondecreasingJointLift/Endpoint.actualSource_two_negative_nondec_joint_lift`
