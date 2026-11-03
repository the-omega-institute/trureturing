# Every natural quadruple with 2<=a,b,c, d=a and b,c<=a

## Abstract

Outer maximum tie: the complete original physical face

**Theorem 1.1 (One physical permutation, one literal fresh insertion, both complete orders).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/OuterMaximumTie/Endpoint.actualSource_outer_maximum_tie_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/OuterMaximumTie/Endpoint.actualSource_outer_maximum_tie_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a,b,c,d in the natural numbers with 2<=a, 2<=b, 2<=c, d=a, b<=a and c<=a, set k=a+b+c+d and s=1+2^a+2^(a+b)+2^(a+b+c). The theorem supplies a permutation sigma of the actual Fin k labels and a natural cut<=k. OriginalOrder(k,s,sigma) and OriginalOrder(k+1,2s,earWord(k,sigma,cut)) hold for those same witnesses. Separately in each row, every finite natural number of repetitions has total zero, and every natural take of every repeated word has sum between zero and modulus(k)/2 or modulus(k+1)/2, respectively. Zero repetitions, zero takes and takes longer than the finite word are all included. The unrestricted Circle problem remains open.

Write t=2^a, y=2^b, z=2^c, D=yz+y+1, A=tD+1, B=t^2(y+1)+t+1, L=zt^2+zt+z+1 and M=tyz+D. The old source modulus is N=t^2yz-1. The inherited charged heads of the new row are 2A, 2B-1, 2L-z-1 and 2M-D. PacketNormalForm.Source and FirstPeakSecondMaximum.Native identify the centered values and native terminal masses on the original labels. The old labels sum to zero in the old row and to -A in the new row. The fresh physical label k contributes A in the new row.

Let U,V,W,X denote the four native chains starting at 0,a,a+c,a+c+b, of lengths a,c,b,a. A mask m denotes the subset of positive physical indices selected by its binary digits, with capacity 2^(length-1)-1. Its complement is capacity-m. Complementary masks partition the actual labels, rather than merely balancing equal values. In particular W mask 1 is the literal singleton [a+c]. The consumed Physical module proves the complete inventory, nodup, signs and paired old/new masses of both packet orders.

The ascending order has terminal sequence X,U,V,W. Its positive banks are full X; U complement v; V complement w; and full W together with U mask v and V mask w. With epsilon=A-M, its old seam vector is [epsilon, B-M-vA, L-M-vA-wB, 0]. Its new seam vector is [2epsilon+D, 2(B-M-vA)+D-1, 2(L-M-vA-wB)+D+w-z-1, 0]. The descending order X,V,U,W uses full X; full V with U mask v and W mask w; U complement v; and W complement w. Its old seams are [epsilon, (v+1)A-M+(w+1)L-B, (w+1)L-M, 0], and its new seams are [2epsilon+D, 2((v+1)A-M+(w+1)L-B)+D-z-w(z+1), 2((w+1)L-M)+D-(w+1)(z+1), 0]. Fresh is literally first in these interior constructions.

Allocation constructs integer masks satisfying their physical stock bounds and both rows' seam windows, without a feasibility hypothesis. The new ascending cases have b<=c<a and b+2<=a, and split by c=b, c=b+1 and c>=b+2; descending wide cases have c<b and b+2<=a. On the separated critical wall b+1=a with c+2<=b, two remainder translates cover the full admissible interval. Write delta=2A-L, C4=2L+z-2D-2, J=B-L-epsilon, v0=ceil(J/A) and R=v0*A-J. The switch chooses (v,w)=(v0,0) when 4R<=C4 and (v0-2,1) otherwise. The proved margins give 0<=R-w*delta and 4(R-w*delta)<=C4. The switch moves the physical W bit 0 and changes the U mask by 2; it does not remove two U occurrences. Its old/new second-seam changes are -delta and -2delta-(z+1). The adjacent critical case b=c+1 uses the separately proved v=2,w=0 allocation.

The certificate connects the actual bank masses to all four old and new finite endpoint checks. Old N is odd, so the inequalities 0<=seam and 2*seam<=head-1 are exactly the lower seam and upper peak constraints at N/2; the charged row uses N. Nonnegative positive-bank increments make each internal prefix lie between the checked endpoints. The native physical permutation is transported to Fin k without relabeling occurrences by values. Equality faces c=a and b=a reuse EqualOuterThree and EqualFirstTwoLast; the remaining balanced face reuses BalancedGaps. Together with the new interior cases, these branches exhaust the original face. The existing SecondPeakMiddleGap zero_period_transport supplies all repetition, take and separate zero-total consequences from the two complete orders.

The connection to group actions is through the existing doubling orbit underlying actualSource: the proof keeps the original orbit labels while changing their linear order and inserting one genuinely new label. The remainder switch is a concrete change of physical allocation with an explicitly computed paired seam displacement. This explains why matching uncharged sums alone is insufficient: the inherited new-row charge must be preserved simultaneously. The construction is a repository synthesis of the supplied route and existing library results; no claim of literature novelty or official acceptance is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/OuterMaximumTie/Endpoint.actualSource_outer_maximum_tie_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/BalancedGaps/Endpoint](../BalancedGaps/Endpoint.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/EqualFirstTwoLast/Endpoint](../EqualFirstTwoLast/Endpoint.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/EqualOuterThree/Endpoint](../EqualOuterThree/Endpoint.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakMiddleGap/Endpoint](../SecondPeakMiddleGap/Endpoint.md)
