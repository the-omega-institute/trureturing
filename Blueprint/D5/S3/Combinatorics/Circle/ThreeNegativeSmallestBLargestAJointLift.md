# The complete strict chamber

## Abstract

One physical order throughout the strict smallest-b largest-a chamber

**Theorem 1.1 (Every 2<=b<c<a).**

Lean statement: `D5/S3/Combinatorics/Circle/ThreeNegativeSmallestBLargestAJointLift.actualSource_three_negative_smallest_b_largest_a_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ThreeNegativeSmallestBLargestAJointLift.actualSource_three_negative_smallest_b_largest_a_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural a,b,c with 2<=b<c<a, put k=a+b+c and u=1+2^a+2^(a+b). There exist one list sigma of Fin(k) labels and one natural j<=k satisfying OriginalOrder(k,u,sigma) and OriginalOrder(k+1,2u,earWord(k,sigma,j)). These assertions include permutation of every physical label, both complete integer totals equal to zero, and bounds on every natural prefix, including overlong prefixes. The fresh label is k, inserted at literal position j; every old label uses the identity embedding castSucc.

The implementation reuses the physical paired-chain table and realizer of ThreeNegativeMinimumTwoJointLift. With r=2^a,s=2^b,t=2^c,N=rst-1,C=(N-1)/2,B=1+t+tr,L=1+s+st, the U,V,W pairs are (u*2^i,2u*2^i),(B*2^i,(2B-1)*2^i),(L*2^i,(2L-s-1)*2^i). Their physical starting indices are 0,c,c+b and their lengths are c-1,b-1,a-1. The negative labels are alpha=c-1,beta=c+b-1,gamma=k-1. The new source table follows from chains at (a,b,c+1) with literal index shift by one. This uses the full physical length even for nonunits or shorter numerical periods.

For b=2 the complete minimum-two result applies directly. Otherwise s>=8. In the far branch a>=c+2, let p=(s-1)t/(2s), lambda=2L-s-1 and z=floor((K_beta-u)/lambda). The masks are P=(p,0,0),T=(0,0,z), with Q the physical complement, negative order (alpha,gamma,beta), and the ear before T. The masks lie in different chains. The floor remainder R lies in [0,lambda), and delta=H_beta-Lz satisfies 0<2delta<u-1. Polynomial expansions establish the bound when t>=4s or r>=8t; the remaining corner r=4t,t=2s has z=r/2-4. Its exact values are 2delta=6s^2-s+6 and u-1-2delta=2s^2+9s-6. The corrected far polynomial at r=8t is 4s(s+2)t^2-(14s^2+23s+8)t-2(s+1)(s+2).

For a=c+1 put q=t/s, h=3 when q=2 and h=q otherwise, and T=(0,0,t-h). Set e=2s(q-1)-1,G=C mod u. The W mask w is zero when q<=s/2, three when q=s, four when q=2s, and 2ceil((u-G)/e) when q>=4s. Set p=floor((C-Lw)/u),P=(p,0,w), use negative order (beta,alpha,gamma), and insert the ear before Q. Dyadic powers make these cases exhaustive. The exact remainder R=C-up-Lw is nonnegative, and 2R+(s+1)w<=st+s/2-1. In the unbounded ceiling branch the integer estimate is <=4sq+2s^2+2s. The W tail t-q is divisible by q for q>=4, whereas w<q; their binary supports are disjoint. The q=2 case has w=0.

The eight old/new seam inequalities are proved for these explicit masks. Positive block interiors are monotone; the realizer then supplies the single old permutation and its literal fresh ear. Complete physical inventory and the actual source-zero identities give both integer totals. The source registration retains all three independent natural coordinates and all six original binders, with the old and new readouts as separate roles. Continuation is unknown. This result is a chamber of the ongoing research on Conjecture 3.1 of Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2; it does not settle full C3.1/J and makes no literature novelty claim.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/ThreeNegativeSmallestBLargestAJointLift.actualSource_three_negative_smallest_b_largest_a_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/ThreeNegativeMinimumTwoJointLift](ThreeNegativeMinimumTwoJointLift.md)
- Dependency: [D5/S3/Combinatorics/Circle/ThreeNegativeSmallestBLargestAAdjacent](ThreeNegativeSmallestBLargestAAdjacent.md)
- Dependency: [D5/S3/Combinatorics/Circle/ThreeNegativeSmallestBLargestAFar](ThreeNegativeSmallestBLargestAFar.md)
