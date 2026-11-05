# One physical permutation for both centered sources

## Abstract

Charge-corrected masks on the cone c<a<b

**Theorem 1.1 (The complete unbounded ordered cone).**

Lean statement: `D5/S3/Combinatorics/Circle/ThreeNegativeSmallestCLargestBJointLift.actualSource_three_negative_smallest_c_largest_b_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ThreeNegativeSmallestCLargestBJointLift.actualSource_three_negative_smallest_c_largest_b_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural a,b,c satisfying 2<=c<a<b, let k=a+b+c and u=1+2^a+2^(a+b). There exist one list sigma of Fin(k) labels and a natural j<=k satisfying OriginalOrder(k,u,sigma) and OriginalOrder(k+1,2u,earWord(k,sigma,j)). Each order permutes every physical label, has integer total zero and bounds every natural take-prefix between zero and half its own modulus. The ear inserts the single fresh label k at position j and embeds every old label by its original index. No coprimality or numerical-period assumption is imposed; repeated centered values remain distinct physical labels.

The boundary c=2 uses the complete minimum-two construction at the unchanged k. For c>=3 put r=2^a,s=2^b,t=2^c,N=rst-1,C=(N-1)/2,B=1+t+tr,L=1+s+st. The three positive physical chains have values u*2^i,B*2^i,L*2^i. Under the doubled source these become 2u*2^i,(2B-1)*2^i,(2L-s-1)*2^i. Thus a mask y has charge q(y)=yV+(s+1)yW and doubled mass 2f(y)-q(y). The negative labels alpha=c-1,beta=c+b-1,gamma=k-1 have old magnitudes Ha=(N-B)/2,Hb=(N-L)/2,Hg=(N-u)/2; their new magnitudes are 2Ha+1,2Hb+s/2+1,2Hg+(u+1)/2. These physical identities and the general conversion of a mask certificate into both orders are reused from the minimum-two module.

Write p=s/r and h=r/t. All four branches use the literal word [P,beta,Q,gamma,T,alpha], with the ear immediately after beta at j=|P|+1. The masks are triples in U,V,W order. If h=p=2, choose P=(1,2t-5,0),T=(t/2-2,4,1). If h=2 and p>=4, choose P=(0,s/2-p+p/4,0),T=(t/2-1,p/2,1). If h=4, choose P=(0,s/2-p,0),T=(t/2-1,0,3). If h>=8, choose P=(0,s/2-p,0),T=(t/2-1,0,m), where m=floor((u-B)/L). The powers of two exhaust these alternatives. Each mask fits its physical chain. In the first branch the low bits are removed from full masks; in the second, the P low bit p/4 and T bit p/2 are distinct and the other P bits lie at or above p. In the last two branches P uses V and T uses U,W. Taking Q as the literal physical complement establishes complete inventory.

The seam mechanism is shared by the two sources. Put epsilon=f(P)-Hb, delta=Ha-f(T), A=2epsilon-q(P)-s/2-1 and D=2delta+q(T)+1. The inequalities 0<=epsilon, f(P)<=C, delta>=0, A>=0 and D<=(u-1)/2 suffice. The old seam heights are f(P),epsilon,Hg+delta,delta,Ha,0. The new seam heights, including the ear endpoint, are Kb+A,A,A+u,Kg+D,D,Ka,0. The physical complement Q has nonnegative new mass, so its endpoint also bounds the ear endpoint. Positive-block interiors are monotone. The exact zero totals for the complete physical inventory determine the remaining seams, including when a positive block is empty.

The final branch uses the actual integer remainder delta=u-B-Lm, with 0<=delta<=L-1. Since L>s(t+1) and 0<u-B<rs, one has m(t+1)<r. For t>=8,r>=8t, the inequality r(t-1)>=4(t+1)^2 yields 2(t+1)+m<=r/2; integrality also gives m+1<=r/2. Consequently D<=s[2(t+1)+m]+m+1<=sr/2+r/2=(u-1)/2. This is an estimate for all exponents, rather than a bounded enumeration.

The construction is a repository-derived part of the physical joint-permutation approach to Conjecture 3.1 in Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2. Its new content is the charge-corrected mask allocation on this entire ordered cone. It does not assert literature novelty. Other exponent orders and equality boundaries are outside this theorem; the full physical J goal and full Circle C3.1 remain open.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/ThreeNegativeSmallestCLargestBJointLift.actualSource_three_negative_smallest_c_largest_b_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/ThreeNegativeMinimumTwoJointLift](ThreeNegativeMinimumTwoJointLift.md)
