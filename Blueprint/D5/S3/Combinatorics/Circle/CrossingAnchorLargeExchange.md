# The native crossing label supplies the bridge

## Abstract

The actual crossing label supplies both retained negative gates in the native three-negative residual with arbitrary q status, retaining every SMALL occurrence.

**Theorem 1.1 (Full native exchange with unchanged SMALL inventory).**

Lean statement: `D5/S3/Combinatorics/Circle/CrossingAnchorLargeExchange.actualSource_threeNegative_crossingAnchor_exchange_full`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/CrossingAnchorLargeExchange.actualSource_threeNegative_crossingAnchor_exchange_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use physical labels Fin k for every k>=3 and the centered doubling source s(k,t), for arbitrary natural t. The source cycle has Q=2^(k-2), N=4Q-1 and C=2Q-1. The source action rho includes its physical seam. Set n=rho(p) and x=rho(n). The old word W=A++[x]++T0++[y]++T1++[zpen]++T2++[z]++E is Legal from zero, including Nodup and every natural take. The whole S=T0++T1++T2++E is SMALL, while y,zpen,z are negative LARGE. The prefix A is arbitrary. The actual labels p,n are unused in ALL W, p is positive, n is LARGE, and N<3s(p). Native source geometry derives P=s(p), D=-s(n), r=s(x), with Q<=D<P<r<=C, D=N-2P and r=2P-D.

The actual crossing label a belongs to S and has aa=s(a)>0. Its actual successor is q=rho(a), with qq=s(q)<=P and arbitrary membership in W. Write ZZ=-s(zpen), Z=-s(z) and h=sum(W). Assume D<=ZZ, Q<=Z<=D, C-qq<h<aa-(ZZ-D), and C-P<h<D. There is no q-to-zpen source-edge premise: zpen may have arbitrary predecessor geometry. No first-crossing, maximality or favorable-path availability assumption is added. The source law derives qq=2aa because a is positive SMALL. Thus D=N-2P<=N-4aa, and delta=ZZ-D>=0. Equality qq=P and delta=0 are allowed. The upper crossing inequality implies h<aa-delta<Q.

Omit an actual largest negative j among [y,zpen,z], breaking a numerical tie by its physical occurrence. The retained physical pair v1,v2 has maximum magnitude M<=ZZ because Z<=D<=ZZ. Put c=C-M. Integer crossing bounds C-2aa<h<aa-delta give 3aa>=2Q+delta+1. Since ZZ=D+delta<=N-4aa+delta, this yields ZZ<=2Q-aa-2. Consequently aa<C-ZZ, 2ZZ<aa+C and 3ZZ<2C, including delta=0. Therefore the ACTUAL label a satisfies the strict bounds 0<aa<c, M<aa+c and M<2c. This is the required bridge resource with no bound on the number or mass of Bad positive SMALL labels.

Old legality at x gives a0=sum(A)>=0 and a0+r<=C. The inserted pair [p,n] is legal and ends at b=a0+P-D in [0,Q-1]; its intermediate height is a0+P. The exact prospective endpoint is e0=h-s(j)-P. The old blocking bounds and the native budget 2P<=C+Q imply 0<e0<C. The physical suffix partition gives b+sum(S)+s(v1)+s(v2)=e0. Apply the crossing-anchor ordering to ALL S and both retained negatives. It constructs L with (L++[j]).Perm(T0++[y]++T1++[zpen]++T2++[z]++E). The complete new word is literally V=A++[p,n]++L, returning EXACTLY [x,j] and inserting EXACTLY [p,n]. The endpoint need not satisfy e0<=c.

Every old prefix in A remains literal; both new source gates and every take of L are checked from their actual start. Thus V is Nodup, Legal and InStrip from the ORIGINAL zero, and every natural take, including empty and overlength takes, lies in [0,C]. All old SMALL, including every Bad occurrence, remain. The total physical permutation (V++[x,j]).Perm(W++[p,n]) gives Inventory: exact disjoint used and unused partitions, source balance and complement mass. Only the FULL physical source total zero is used to obtain remainingMass(V)=-e0. No proper source subset is assigned zero charge.

Both returned and both inserted occurrences are LARGE. Therefore G(V)=G(W), U(V)=U(W), and remainingSmall(V)=remainingSmall(W). The sparse identity is H(V)+3^|s(x)|+3^|s(j)|=H(W)+3^P+3^D. The native expanding path gives 3^P+3^D<3^r, whence strict H(V)<H(W) and strict J=(G,H,U) descent. The source law gives q positive with qq<=P<r, so q differs physically from returned x and negative j and from inserted negative n. The full physical permutation therefore proves the exact status formula q in V iff (q in W or q=p). This covers q already in A, q unused, and q=p entering V as inserted p, including periodic sources and numerical ties without identifying physical labels. The endpoint is exactly e0 in (0,C).

At a genuine global J minimum, this complete exchange excludes every representative with the stated native configuration, without requiring a chosen representative with few Bad labels. The theorem closes this native qq<=P, D<=ZZ, three-negative-LARGE region with arbitrary q status and no q-to-zpen edge. It does not prove that the stated actual crossing, penultimate or magnitude conditions always occur. The qq>P and ZZ<D regions, mixed or other geometries, longer source paths, suffixes with four or more negative LARGE, and global favorable-path availability remain outside its conclusion. Full original-quantifier Circle C3.1 remains open. The result is a deduction in the stated mathematical source theory, without a literature novelty claim.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/CrossingAnchorLargeExchange.actualSource_threeNegative_crossingAnchor_exchange_full`
- Dependency: [D5/S3/Combinatorics/Circle/CrossingAnchorOrdering](CrossingAnchorOrdering.md)
