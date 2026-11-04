# The entire family 2<=c<a=b

## Abstract

A physical joint order when the first two gaps are equal and the last is smaller

**Theorem 1.1 (One physical permutation and one literal fresh ear).**

Lean statement: `D5/S3/Combinatorics/Circle/ThreeNegativeEqualInnerSmallCJointLift.actualSource_three_negative_equal_inner_small_c_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ThreeNegativeEqualInnerSmallCJointLift.actualSource_three_negative_equal_inner_small_c_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all independent natural coordinates a,b,c with 2<=c, a=b and c<a, put k=a+b+c and u=1+2^a+2^(a+b). There exist one permutation sigma of the original Fin(k) labels and a natural j<=k such that OriginalOrder(k,u,sigma) and OriginalOrder(k+1,2u,earWord(k,sigma,j)). Both complete integer sums are zero. Every natural take-prefix, including the empty and overlong prefixes, lies between zero and half the corresponding modulus. The inserted label is literally k; old labels retain their original indices via castSucc. The physical length is never replaced by a shorter numerical period.

The entire boundary c=2 reuses actualSource_three_negative_minimum_two_joint_lift. The new construction assumes c>=3. Write r=2^a=2^b, t=2^c>=8, q=2^(a-c), N=r^2*t-1, C=(N-1)/2, B=1+t+tr and L=1+r+rt. The actual source chains have labels U_i=i, V_i=c+i and W_i=c+b+i, with lengths c-1,b-1,a-1. Their paired old/new values are (u*2^i,2u*2^i), (B*2^i,(2B-1)*2^i), and (L*2^i,(2L-r-1)*2^i). The three negative labels are alpha=c-1, beta=c+b-1 and gamma=k-1, with old magnitudes H_alpha=(N-B)/2, H_beta=(N-L)/2 and H_gamma=(N-u)/2. Their new magnitudes are K_alpha=2H_alpha+1, K_beta=2H_beta+r/2+1 and K_gamma=2H_gamma+(u+1)/2. The fresh new value is u. These physical identities and both source totals are reused through the existing generic paired-chain realization.

Set lambda=2L-r-1, Y=K_beta-u and z=floor(Y/lambda). The first positive block has binary masks P=(t/2-1,q-1,0), and the tail has masks T=(0,0,z). The middle block Q is the literal complement of these physical supports and the three negative labels. The negative order is (alpha,gamma,beta), so sigma=[P,alpha,Q,gamma,T,beta]. The ear is inserted at the start of T, at j=|P|+1+|Q|+1=k-1-|T|. Each block uses the fixed physical enumeration supplied by the existing support machinery; its interior heights are monotone because all its paired values are positive.

The floor proof is unbounded. Put r=4m and t=2n, where n>=4 and m>=n. Then lambda=16mn+4m+1, Y=32m^2*n-16m^2-8mn-6m-2, u=1+4m+16m^2. Positivity gives Y>0 and Y<lambda*(2m), hence 0<=z<2m=r/2. Let R=Y-lambda*z and h=(r+1)z+r/2+1. Exact Euclidean division gives 0<=R<lambda. The mask bound gives h<=8m^2=r^2/2. The essential additional estimate is R<h; it follows from the following exhaustive dyadic alternatives.

If a=c+1, then m=n, lambda=u, Y=lambda*(2n-2), z=2n-2=t-2 and R=0. If a=c+2, then m=2n, z=4n-4=2t-4 and R=16n^2+16n+2. Here 0<=R<lambda and h-R=16n^2-40n-5>0 for every n>=4. Otherwise a>=c+3 and m>=4n. Expanding Y-lambda*(m+1) in the nonnegative variables m-4n and n-4 proves it nonnegative; thus z>=m+1. Consequently h-lambda>=3m+1>0, so h>R. The exponent cases cover every q=2, q=4 or q>=8; no upper bound, residue search or cyclic phase symmetry is assumed.

The first margins are epsilon=o(P)-H_alpha=q-1 and A=n(P)-K_alpha=q-2. They are nonnegative and o(P)<=C. For the tail, define delta=H_beta-Lz. The exact identities are D=K_beta-lambda*z=u+R and 2delta=u+R-h. Since h<u and 0<=R<h, delta>=0 and 2delta<=u-1. Also R<h<=r^2/2<=(u-1)/2. These inequalities prove all eight actual seams: H_alpha<=o(P)<=C, Lz<=H_beta, H_gamma+H_beta-Lz<=C; K_alpha<=n(P)<=N, lambda*z+u<=K_beta, K_gamma+K_beta-(lambda*z+u)<=N. In particular the two insertion-adjacent heights are R and D=u+R. The six mask capacities follow from n-1<n, q-1<r/2 and 0<=z<r/2. Disjointness is literal because P uses only U and V, while T uses only W. The generic realization consumes this certificate, enumerates the physical complement, proves both integer totals and all natural prefixes, and constructs the same sigma and literal earWord.

This is a repository-derived construction in the study of Conjecture 3.1 of Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2. It makes no literature novelty claim. Its exact scope is 2<=c<a=b; full Circle C3.1 and the full physical-J goal remain open.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/ThreeNegativeEqualInnerSmallCJointLift.actualSource_three_negative_equal_inner_small_c_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/ThreeNegativeMinimumTwoJointLift](ThreeNegativeMinimumTwoJointLift.md)
