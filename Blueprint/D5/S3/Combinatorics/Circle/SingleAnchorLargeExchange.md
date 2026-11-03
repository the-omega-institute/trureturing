# A single physical anchor supplies the return interval

## Abstract

An actual positive SMALL anchor constructs the complete physical three-LARGE exchange, with integer-sharp bounds and no assumed doubling pair or returned subset.

The source labels are Fin k with k>=3 and actualSource(k,t) for arbitrary natural t. The cyclic permutation rho includes its seam and sets n=rho(p), x=rho(n). For a positive p with Q<=|s(n)| and N<3s(p), native source geometry gives s(p)=P>0, s(n)=-D and s(x)=r, with Q<=D<P<r<=C, D=N-2P and r=2P-D. Grouping and permuting actual word occurrences preserves their physical labels and weighted sums. The cyclic source action fixes arithmetic successors; the retained word order is supplied by a permutation of its physical list. Distinct labels remain distinct even when their values agree.

**Theorem 1.1 (Full exchange from one actual positive SMALL anchor).**

Lean statement: `D5/S3/Combinatorics/Circle/SingleAnchorLargeExchange.actualSource_threeLarge_singleAnchor_exchange_full`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/SingleAnchorLargeExchange.actualSource_threeLarge_singleAnchor_exchange_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual Legal word is exactly W=A++[x]++T0++[y]++T1++[zpen]++T2++[z]++E. All entries of S=T0++T1++T2++E are SMALL. The later LARGE labels y,zpen,z are negative, with Q<=Y=-s(y), Q<=ZZ=-s(zpen) and Q<=Z=-s(z)<=qq=s(q). The label q is positive LARGE with qq<P, and all three inserted labels p,n,q are unused in the whole W. The original prefix A is arbitrary and is retained literally. The theorem keeps the source gates Q<=|s(n)| and N<3s(p); it adds no gate on a selected return list or on a new endpoint.

The actual anchor a belongs to S and has positive integer value m=s(a). Put B=C-qq. Require m<=B+1 and, for each OTHER actual positive SMALL occurrence i in S, s(i)<=m+B+1. The anchor need not occur at any specified position within S, and no actual after-x doubling pair is a hypothesis. These are resource conditions on actual source labels; the theorem does not assert that an adequate anchor always exists.

The selector removes exactly the occurrence a from Pos, the full positive filter of S, leaving O with (O++[a]).Perm(Pos). For a positive demand low<=sum(Pos), if low<=m use the empty O-prefix. Otherwise reuse the first-crossing construction on the actual O with threshold low-m. Before the last selected entry the integer mass is at most low-m-1; each other entry is at most m+B+1, so its crossing mass u is at most low+B. Thus low-m<=u<=low+B. If u>=low, return the crossing prefix alone. If u<low, append precisely the reserved actual a: low<=u+m<=low-1+m<=low+B. Both cases construct a physical Subperm of Pos and retain its full complement. The +1 constants come from the strict integer pre-crossing inequality.

Old legality gives the original height a0=sum(A) and a0+r in [0,C]. The actual inserted pair [p,n] is legal, with b0=a0+P-D in [0,C-P]. Let h=sum(W) and e0=h+Y+ZZ+qq-P=b0+sum(S)-Z+qq. Because Y+ZZ>=2Q=C+1>P and h>=0, e0>qq. The mass of all positive entries of S dominates sum(S); together with b0<=C-P and qq<P this supplies demand low=e0-C whenever e0>C. Applying the constructed single-anchor selector gives low<=sum(R)<=low+B. When e0<=C use R=[]. In both cases e=e0-sum(R) lies in [qq,C]. The positive-mass estimate is a scalar identity and does not presume any intermediate word legal.

Set eta=e-qq and c=eta+Z. Then 0<=eta<=c<=e<=C. Remove exactly R from S, keeping Rem=S.diff(R) and (Rem++R).Perm(S). Exact mass gives b0+sum(Rem)=c. Since every opposite SMALL pair differs by at most 2Q-2<C, the SMALL ordering theorem orders the WHOLE remaining physical batch Rem from b0 to c. Its order L satisfies (L++R).Perm(S). Retained z takes c to eta and appended q takes eta to e. The complete word V=A++[p,n]++L++[z,q] is Legal, with InStrip from the original zero and the bounds for every natural take, including empty and overlength takes.

The returned list is exactly [x,y,zpen]++R and the inserted list exactly [p,n,q]. Old Nodup and whole-word unusedness prove every physical join disjoint. Inventory gives the complete used and unused partitions, source/complement sums and SMALL complement update. Precisely, used(V) is used(W) with the returned labels removed and the inserted labels added; unused(V) has the reverse update. All R labels are positive SMALL. Thus G(V)=G(W), U(V)=U(W)+length(R), and H(V)+3^|s(x)|+3^|s(y)|+3^|s(zpen)|=H(W)+3^|s(p)|+3^|s(n)|+3^|s(q)|. Since D,qq<P<r, the three inserted energies together are strictly below 3^r. Consequently H(V)<H(W) and J(V)<J(W) for the priority J=(G,H,U), even when U increases. The endpoint is exactly e0-sum(R), and the complete unused source has its negative mass.

This is a complete conditional exchange for exactly three later negative LARGE labels. The actual single-anchor construction is used to obtain the returned physical batch; no returned subset, after-x doubling pair, minimizer, append blocking or legal new endpoint is assumed. Genuine-minimality availability of an adequate actual anchor, or an alternative exchange when no anchor exists, remains OPEN. The theorem neither handles arbitrarily many later LARGE labels nor proves full C3.1. It is a deduction within the stated source theory, without a literature novelty claim.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/SingleAnchorLargeExchange.actualSource_threeLarge_singleAnchor_exchange_full`
- Dependency: [D5/S3/Combinatorics/Circle/ThreeLargePacketExchange](ThreeLargePacketExchange.md)
