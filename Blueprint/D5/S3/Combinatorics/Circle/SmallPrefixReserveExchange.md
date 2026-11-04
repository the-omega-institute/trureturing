# An actual prefix reserve and the remaining prefix obstruction

## Abstract

An actual negative SMALL prefix reserve supplies a complete three-LARGE exchange after its compatible physical suffix is reordered.

**Theorem 1.1 (Full physical exchange from a negative SMALL prefix reserve).**

Lean statement: `D5/S3/Combinatorics/Circle/SmallPrefixReserveExchange.actualSource_threeLarge_smallPrefixReserve_exchange_full`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/SmallPrefixReserveExchange.actualSource_threeLarge_smallPrefixReserve_exchange_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k,t be natural, k>=3, N=2^k-1, Q=2^(k-2), C=2Q-1, and f the actual centered source on physical Fin k labels. Put n=rho(p), x=rho(n), P=f(p)>0 and D=|f(n)|. Assume n is LARGE and N<3P. Native source geometry gives f(n)=-D, f(x)=r, Q<=D<P<r<=C, N=2P+D and r=2P-D. There is no unit or injectivity hypothesis: distinct labels can have equal values, and zero-valued entries are allowed.

The original Legal word is W=A++[x]++T0++[y]++T1++[zpen]++T2++[z]++E, with S=T0++T1++T2++E entirely SMALL and y,zpen,z negative LARGE. The labels p,n,q are unused in the whole W; q has actual value L with Q<=L<P, and Z=-f(z)<=L. A is arbitrary and may contain earlier LARGE. No first-LARGE, maximal-LARGE, global-minimum, odd-y or first-valley hypothesis is imposed on this exchange.

Suppose A=Aminus++[c]++K, f(c)=-m, 1<=m, L-Q-1<=m<B=C-P, and mass(A)+m<=B (GATE). Suppose the whole actual K satisfies f(i)-f(j)<=C whenever i,j belong to K and f(i)>0>f(j) (COMP). These are hypotheses about an actual physical reserve, its final gate and its actual suffix; no new word, return list, supply or order is assumed.

Put u=mass(Aminus). The old Legal prefix places u in [0,C], while GATE places mass(A)+m in [0,B]. The total mass of K is mass(A)+m-u. The compatible-list ordering theorem constructs Kstar.Perm K between these endpoints. Thus Astar=Aminus++Kstar is legal from zero, mass(Astar)=mass(A)+m, and (Astar++[c]).Perm A. Its next two heights, mass(A)+m+P and bstar=mass(A)+m+P-D, lie in [0,C], with 0<=bstar<=C-D. All earlier LARGE are retained; their order may change.

Set F=[c]++S. Its Nodup property follows from its physical sublist inclusion in W; m<B<Q makes c SMALL. Define e0=bstar+mass(F)-Z+L. Exact original-word mass cancellation gives e0=mass(W)+Y+Zpen+L-P, where Y=-f(y) and Zpen=-f(zpen). Since Y+Zpen>=2Q=C+1>P and mass(W)>=0, e0>L. The extracted -m is counted exactly once.

Let Pos be the positive filter of F. Its mass dominates mass(F). Consequently e0-mass(Pos)<=C-D-Z+L<C, because D+Z>=2Q=C+1>L. If e0>C this proves the actual positive supply low=e0-C< mass(Pos). Apply signed_short_reserve_select to the actual F with P0=[], N0=[c], width C-L, and entry bound Q-1. The negative short condition follows from m<B<C-L+1, and its exact resource inequality is (Q-1)-(C-L)-1=L-Q-1<=m. It constructs (R++Ksmall).Perm F with low<=mass(R)<=low+C-L. If e0<=C, use R=[] and Ksmall=F. Both branches give L<=e=e0-mass(R)<=C.

Write eta=e-L and endSmall=eta+Z. The inequalities Z<=L and L<=e<=C give 0<=eta<=endSmall<=e<=C. The complete actual Ksmall takes bstar to endSmall; all its entries are SMALL, hence opposite pairs are compatible. Order this whole batch as Lsmall.Perm Ksmall. The literal word V=Astar++[p,n]++Lsmall++[z,q] is Legal: its final two gates reach eta and e. Every natural take is bounded, including takes beyond the length. No translated old SMALL order is used.

The exported witnesses are Kstar, R, Ksmall and Lsmall. For I=[p,n,q] and Ret=[x,y,zpen]++R, the exact original-word permutation is (V++Ret).Perm(W++I). The existing physical Inventory theorem supplies the disjoint used and unused partitions, source mass balance and complement sum. Both V and Ret are Nodup and no returned label remains in V. The remaining SMALL inventory is remainingSmall(W) disjoint-union R; every LARGE from the original A remains in V.

SMALL weights vanish. Inventory therefore gives G(V)=G(W), U(V)=U(W)+length(R), and H(V)+3^|f(x)|+3^|f(y)|+3^|f(zpen)|=H(W)+3^P+3^D+3^L. Integral D,L<P<r imply 3^P+3^D+3^L<3^(P+1)<=3^r. Hence H(V)<H(W) and J(V)<J(W), independently of length(R). Finally mass(V)=e and mass(unused(V))=-e. All comparisons use the original W and original source.

## Application at a genuine global minimum in the odd unused-parent residual

Now use the root residual with odd Y=-f(y)>P, whole-unused physical beta=rho^(-1)(y), L=f(beta)=(N-Y)/2, delta=Y-P>=1, d=P-D, endpoint B<h=mass(W)<D, first valley v<d, D<=3d-4, Z<=D<L, and an actual positive SMALL crossing after zpen. This is the specified residual branch; first-valley and crossing hypotheses are not asserted for every original word. Let W be a genuine global minimum of J among all Legal physical words, without fixing its endpoint, used set or LARGE order.

The actual crossing a has f(a)+Z>C, so its physical successor has value 2f(a)>r. The next actual successor b0 has f(b0)=-m0 with 1<=m0<=D-2d-2<=d-6. Put Rreq=L-Q-1=(D-2delta-5)/4, using N=3D+2d and 4Q=N+1. If Rreq<=0 the empty signed reserve suffices. If Rreq>0, take the first actual dyadic iterate c=b_j with m=2^j*m0>=Rreq. When j>=1, first crossing gives m<=2Rreq-1=B-delta-3<B; when j=0, m=m0<=d-6<B. All earlier magnitudes are smaller than Q, so these are genuine inner negative doubling steps on physical labels.

Since 0<m<B<mass(W), an unused such c could be appended legally, preserving G,H and decreasing U. Thus c is already used. Its negative SMALL value excludes x,y,zpen,z. If c lies in S, the existing signed-short exchange with N0=[c] gives strict descent. Therefore a qualifying actual c lies in the original A, which decomposes literally as Aminus++[c]++K. No location is inferred merely from equality of numerical values.

For every such occurrence c, the full exchange proves that global minimality forces either mass(A)+m>B (gate failure), or an actual pair i,j in the literal suffix K with f(i)>0>f(j) and f(i)-f(j)>C. Two SMALL opposite entries have difference at most 2Q-2<C; the incompatible pair therefore contains at least one LARGE after c. It may consist of two LARGE, or one LARGE and an incompatible opposite SMALL. COMP is not automatic, even if all LARGE in K have one sign.

The gate failure cannot occur if j=0, since mass(A)<=B-d and m0<=d-6. For j>=1, m<=B-delta-3 makes the gate failure imply mass(A)>=delta+4. If D<=2d+2delta+7, then 2Rreq-1<=d, again forcing GATE. Thus COMP closes the residual whenever j=0, or mass(A)<=delta+3, or D<=2d+2delta+7.

Outside these closures a COMP-compatible suffix at a genuine minimum must satisfy all of j>=1, mass(A)>=delta+4, D>2d+2delta+7, and m>=B-mass(A)+1>=d+1. Its actual dyadic predecessor has magnitude m/2, with d/2<m/2<Rreq; it is not thereby located in S and is not an adequate reserve. The incompatible-pair alternative and this high-prefix, larger-reserve strip remain open. Excluding either requires additional mathematical content; the conditional exchange does not prove full C3.1.

## Why the old suffix order cannot be retained

For the actual source k=60, t=422782879156513670, take A=[22,4,26,27,11,21], c=27 and K=[11,21]. Here C=576460752303423487. Removing c while keeping K's order creates the height 582092180215424290>C, despite COMP and GATE. Reordering K as [21,11] gives the full competitor [22,4,26,21,11,0,1,27,25,20,36,5,23], returning physical [2,24,18,55,15] and inserting [0,1,23]. This configuration is not a global minimum. The analogous actual source k=120, t=422782879156513670*(2^60+1), is nonunit with repeated values at distinct labels. These examples explain why physical permutations and complete reordering, rather than numerical label identification or the old K order, are essential.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/SmallPrefixReserveExchange.actualSource_threeLarge_smallPrefixReserve_exchange_full`
- Dependency: [D5/S3/Combinatorics/Circle/SignedShortLargeExchange](SignedShortLargeExchange.md)
