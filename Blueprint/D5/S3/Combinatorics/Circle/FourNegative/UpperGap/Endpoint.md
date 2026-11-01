# The fourth gap exceeds all three independent earlier gaps

## Abstract

Physical four-gap upper-gap joint orders

**Theorem 1.1 (One old physical permutation and one literal ear cut).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/UpperGap/Endpoint.actualSource_upper_gap_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/UpperGap/Endpoint.actualSource_upper_gap_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural a,b,c>=2 and d>max(max(a,b),c), put k=a+b+c+d and A=1+2^a+2^(a+b)+2^(a+b+c). There exist one list sigma of Fin(k) and one natural j<=k such that OriginalOrder(k,A,sigma) and OriginalOrder(k+1,2A,earWord(k,sigma,j)) both hold. Each OriginalOrder includes the permutation of every physical occurrence, the exact zero total, and bounds on every natural take-prefix, including empty, complete and saturated takes. Equal source values do not identify labels.

On the boundary d=max(max(a,b),c)+1 the construction partitions actual positive labels by binary masks and follows each bag by its own negative terminal. The weak middle maximum includes a=b, b=c and a=b=c, using an even floor for the first mask and an adjacent or ceiling mask at the last nontrivial packet. The last weak-peak mask has w<2^(b-1); hence its doubled transfer charge 2w(2^c+1) is bounded by 2^b(2^c+1), which closes the enlarged final peak. The strict first maximum uses an even floor when b<c and a multiple of 2^(a-b) when c<=b, retaining b=c. The strict rising, swapped rising and tied outer chambers use interval and singleton masks.

When a=b<c the negative terminal order is U,W,V,X. Below c=2a one V singleton moves to the final positive bag. From c=2a onward a second, distinct V singleton moves to the positive bag before the W terminal. Exact integer transport of the polynomial charts proves all old and enlarged packet seams and peaks. The inventory theorem retains every original label once. Both exact source totals and the value of the fresh label place the literal fresh occurrence immediately before the final X terminal.

The exact physical four-packet equivalence transports these constructed packets to the common old permutation and the literal earWord. For d>=max(max(a,b),c)+2 the theorem directly reuses actualSource_max_plus_two_first_ear. The conclusion is a sufficient upper-gap theorem; the unrestricted four-gap J problem remains open.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/UpperGap/Endpoint.actualSource_upper_gap_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Endpoint](../MaxPlusTwo/Endpoint.md)
