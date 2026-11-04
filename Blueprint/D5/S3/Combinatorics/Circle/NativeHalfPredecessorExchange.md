# Full exchange through the physical SMALL source half

## Abstract

Return the actual source half from the last pre-boundary SMALL batch, reordering both entire affected SMALL batches and proving every new gate and exact inventory.

The source is actualSource on physical Fin k with k>=3 and arbitrary natural t. Write n=rho(p), q=rho(a), zpen=rho(q), and b=rho inverse(a), including the cyclic seam. The old Legal word is W=A++S++[zpen]++T++[z]++E0++E1; all entries of S,T,E0,E1 are SMALL, a is in T, b is in S, and n,q are unused in ALL W. The arbitrary original prefix A may contain arbitrarily many LARGE labels and is retained exactly.

**Theorem 1.1 (Construct the full strict-G exchange from three old scalar bounds).**

Lean statement: `D5/S3/Combinatorics/Circle/NativeHalfPredecessorExchange.actualSource_half_predecessor_exchange_full`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/NativeHalfPredecessorExchange.actualSource_half_predecessor_exchange_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the positive odd source region: s(p)=P>0, n is LARGE, N<3P, C+1<3s(a), s(q)<P, and z is negative LARGE with -s(z)<=|s(n)|. Put s(n)=-D, s(a)=aa, s(q)=qq, s(zpen)=-ZZ, s(z)=-Z and delta=ZZ-D. Previously proved native geometry supplies D=N-2P, 2P<=C+Q and Q<=D. The actual source cycle at a and q gives qq=2aa, ZZ=N-2qq, D<qq<P, and delta>0.

The only additional scalar inputs concern old physical prefixes. With B0=C-P, wpen=sum(A++S++[zpen]), and v=sum(A++S++[zpen]++T++[z]++E0), assume B0<wpen, B0<v and v<aa-delta. No legal changed prefix, selected subset, new endpoint, minimizer, append blocking, unusedness of p or earlier odd-exchange branch condition is assumed.

The physical b is SMALL because it occurs in S. Its true successor is a. Therefore the two wrapped LARGE branches of the exact source doubling law are impossible, and 2s(b)=aa. This derives the positive half beta=s(b), rather than assuming evenness or a numerical source profile. The source budget gives beta<=B0; qq<P and aa<Q also give 5aa<=2C-1.

Erase exactly the occurrence b from S. The standard erase permutation proves (S.erase(b)++[b]).Perm(S), including physical multiplicities. Its intended endpoint is fprime=sum(A++S)-beta. Old legality and wpen>B0>=beta give 0<=fprime<=C, while sum(A) is an original legal height. SmallStepOrdering.exists_order_between therefore constructs Sprime.Perm(S.erase(b)) from sum(A) to fprime. Thus the changed prefix A++Sprime is proved legal from zero. Inserting actual n then reaches b0=fprime-D=wpen+delta-beta, which also lies in [0,C].

Put eta=v+delta-beta, e=eta+qq and c=eta+Z. Since v>B0>=beta, eta is positive. The old upper bound v<aa-delta and 5aa<=2C-1 imply e<C; since 0<Z<=D<qq, both c and e lie in [0,C]. Exact old-word mass gives b0+sum(T++E0)=c. The same SMALL ordering theorem constructs L.Perm(T++E0) from b0 to c. Retained z takes c to eta and appended q takes eta to e. This proves InStrip from zero and every natural take bound, including empty and overlength takes, for literal V=A++Sprime++[n]++L++[z,q].

The literal returned list is R=[zpen,b]++E1. The two complete physical permutations prove (V++R).Perm(W++[n,q]). Whole-word unusedness of n,q, their opposite source signs and old Nodup yield the complete Inventory: new Nodup, exact used and unused partitions with disjoint joins, complement/source sums and the SMALL complement update. No equality of numerical weights identifies distinct labels.

Only zpen is returned LARGE, while n,q are inserted LARGE. Hence G(V)+1=G(W), U(V)=U(W)+|E1|, and H(V)+3^|s(zpen)|=H(W)+3^|s(n)|+3^|s(q)|. The precise endpoint is v+delta+qq-beta. The first objective coordinate decreases, so J=(G,H,U) strictly decreases regardless of energy or all-unused-count changes.

This exchange applies when the actual half occurs in the final pre-zpen SMALL batch. It does not establish that a half or another suitable returned label occurs there. Earlier mixed LARGE gates, universal exchange availability, general deep-suffix existence and full C3.1 remain OPEN. The source relation, all affected gates and physical balances are formal outputs of this conditional theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/NativeHalfPredecessorExchange.actualSource_half_predecessor_exchange_full`
- Dependency: [D5/S3/Combinatorics/Circle/TwoOppositeLargeExchange](TwoOppositeLargeExchange.md)
