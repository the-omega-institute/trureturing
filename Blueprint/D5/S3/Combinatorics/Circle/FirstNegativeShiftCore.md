# Complete SMALL-batch physical exchange

## Abstract

Complete SMALL batches give a physical first-negative exchange from translated retained gates and a closed endpoint.

**Theorem 1.1 (Three complete batches with exact physical balances).**

Lean statement: `D5/S3/Combinatorics/Circle/FirstNegativeShiftCore.complete_small_shift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FirstNegativeShiftCore.complete_small_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural k,t with k>=3, use the centered dyadic source on physical labels Fin k. Put n=rho(p), x=rho(n), P=s(p)>0, D=abs(s(n)), Y=-s(y), Q=2^(k-2) and C=2Q-1. Assume n is LARGE, N<3P and the original full word W=A++[x]++T0++[y]++T1++[zpen]++T2++[z]++E is Legal from zero. Both p,n are unused in all W, y is negative LARGE, and every occurrence of T0,T1,T2,E is SMALL. No sign or LARGE premise on the retained zpen,z is required by this theorem.

Let F,Efinal,Extra be SMALL lists with (F++Efinal).Perm(E++Extra) and (W++Extra).Nodup. The extension baseline W++Extra need not be Legal. Set delta=Y+sum(F)-P and e0=sum(W)+Y+sum(Extra)-P. Require e0 in the closed strip [0,C]. For each retained gate zpen,z, require both its actual old departure plus delta and its actual old arrival plus delta in [0,C]. These four translated gate bounds and the closed endpoint are explicit hypotheses, rather than an assumed reordered Legal word.

Native expanding geometry gives s(n)=-D, s(x)=r=2P-D, D<P<r and 2P<=C+Q. Original legality at x proves the literal inserted pair [p,n] legal after A, ending at b=sum(A)+P-D. The first complete batch T0++T1++F joins across the removed y and ends at the translated departure of zpen. The next T2 joins its translated arrival to the translated departure of z. The last Efinal joins the translated arrival of z to e0. Each identity uses full actual old prefixes.

Opposite SMALL weights differ by at most 2Q-2<C. SmallStepOrdering.exists_order_between therefore constructs L01.Perm(T0++T1++F), L2.Perm(T2) and LE.Perm(Efinal), including empty batches. Their strips assemble with the retained gates into L=L01++[zpen]++L2++[z]++LE and V=A++[p,n]++L. Every natural take of V lies in [0,C], including zero and overlength takes. All original SMALL occurrences and the retained labels zpen,z remain.

The exact permutations are (L++[y]).Perm((T0++[y]++T1++[zpen]++T2++[z]++E)++Extra) and (V++[x,y]).Perm((W++Extra)++[p,n]). Inventory(k,t,W++Extra,V,[p,n],[x,y]) proves physical Nodup, Legal(V), the exact used and unused partitions and the absence of returned x,y from V. Equal-valued labels remain separate physical occurrences. The full-source complement gives sum(V)=e0 and remainingMass(V)=-e0.

Extra has zero LARGE weight and energy. Thus G(V)=G(W), U(V)=U(W++Extra), and remainingSmall(V)=remainingSmall(W++Extra). The exact energy balance is H(V)+3^abs(s(x))+3^abs(s(y))=H(W)+3^abs(s(p))+3^abs(s(n)). Native geometry gives 3^P+3^D<3^r, so H(V)<H(W) and J(V)<J(W).

FirstNegativeShiftExchange uses this theorem with F=[], Efinal=E and Extra=[] for the first-negative shift. Its even-half branch uses F=[b], where b is the actual SMALL inverse parent of y: either Extra=[b], Efinal=E for a fresh parent, or Extra=[], Efinal=E.erase(b) for a parent already in E. The same physical construction supplies both cases. These conditional exchanges do not establish general parent availability or full Circle C3.1.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FirstNegativeShiftCore.complete_small_shift`
- Dependency: [D5/S3/Combinatorics/Circle/ThreeLargePacketExchange](ThreeLargePacketExchange.md)
