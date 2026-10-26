# First negative omission from actual arrivals

## Abstract

Omitting the first negative LARGE uses two actual old arrival measurements and complete SMALL-batch reorderings.

**Theorem 1.1 (Full physical exchange retaining every SMALL occurrence).**

Lean statement: `D5/S3/Combinatorics/Circle/FirstNegativeShiftExchange.actualSource_threeNegative_firstNegative_shift_exchange_full`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FirstNegativeShiftExchange.actualSource_threeNegative_firstNegative_shift_exchange_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exchange is conditional on the two actual old arrival measurements stated below. It reuses native_geometry, strip_split, inStrip_append, exists_order_between and inventory_of_perm. The new construction joins the complete T0++T1 batch across the omitted first negative and checks the two retained negative gates at their translated actual endpoints.

For arbitrary k>=3 and natural t, use physical labels Fin k and the full centered dyadic source s(k,t). Put Q=2^(k-2), N=4Q-1, C=2Q-1, n=rho(p), x=rho(n), P=s(p)>0, D=abs(s(n)), r=abs(s(x)). Assume n is LARGE and N<3P. Native geometry proves s(n)=-D, s(x)=r, Q<=D<P<r<=C, D=N-2P, r=2P-D and 2P<=C+Q. The actual old word W=A++[x]++T0++[y]++T1++[zpen]++T2++[z]++E is Legal from ORIGINAL zero, with all natural takes and physical Nodup. Both p and n are unused in all W. A is arbitrary; every occurrence of S=T0++T1++T2++E is SMALL, with abs(s(i))<Q. The three physical occurrences y,zpen,z are negative LARGE. No numerical-source injectivity is assumed.

Write Y=-s(y), a0=sum(A), h=sum(W). Assume C-P<h<D and Y<=P. The two additional measurements are the actual old prefix sums AFTER zpen and AFTER z, each >=C-P. Explicitly they are sum(A++[x]++T0++[y]++T1++[zpen]) and sum(A++[x]++T0++[y]++T1++[zpen]++T2++[z]). These are not sums of suffixes and are not shifted or reordered measurements. Equality with C-P is allowed. The theorem adds no q, a, crossing-band or source-edge premise, no Bad-count premise and no Z<=D premise. It does not assume a new Legal word or an available return batch.

Set delta=Y-P<=0 and b=a0+P-D. Old legality at the physical x gives a0>=0 and a0+r<=C. Thus [p,n] is legal at a0, including its intermediate arrival a0+P; its final height is b in [0,C-P], hence in [0,Q-1]. Let d1,a1 be the old departure and arrival of zpen, and d2,a2 those of z. All four are in [0,C], and a1<=d1, a2<=d2. For each measured arrival a, a+delta>=C+Y-2P>=C+Q-2P>=0. The shifted departures are no lower than the corresponding shifted arrivals; all four shifted heights are <=C because delta<=0. This verifies the retained LARGE gates separately, even if their magnitudes exceed D.

The first COMPLETE batch is T0++T1. Its required endpoints are b and d1+delta, and b+sum(T0++T1)=d1+delta follows exactly from r=2P-D and Y=-s(y). It joins across the omitted FIRST y. One must not translate the intermediate old T0 or T1 prefixes blindly. The next complete batch T2 runs from a1+delta to d2+delta, and the complete final E runs from a2+delta to e0=h+Y-P. Both identities use their full actual old prefixes. The blocking inequalities give e0>C+Y-2P>=0 and e0<D+Y-P<Y<=P<=C, so e0 is strictly interior.

For two opposite SMALL entries i,j, integer strictness gives s(i)-s(j)<=2Q-2<C=2Q-1. Thus exists_order_between applies to EACH complete batch, including empty batches, producing L01.Perm(T0++T1), L2.Perm(T2), LE.Perm(E), with every intermediate height checked at its respective required start. The literal new suffix is L=L01++[zpen]++L2++[z]++LE, and the literal new full word is V=A++[p,n]++L. The proof assembles these strips using inStrip_append, keeping A from its original zero. It obtains InStrip(V), physical Nodup and Legal(V), together with every natural take, including zero and overlength takes. The retained zpen,z remain in that order and y is the first occurrence omitted, regardless of which negative magnitude is largest.

Complete-batch permutations give (L++[y]).Perm(T0++[y]++T1++[zpen]++T2++[z]++E) and the exact whole-word permutation (V++[x,y]).Perm(W++[p,n]). inventory_of_perm supplies exact disjoint used and complementary unused partitions, source balance and physical Nodup. It also verifies that x,y are actually absent from V and that zpen,z are present. All S and every old SMALL in A remain; no SMALL occurrence is returned. The full physical source, not a proper subset, has total zero. Consequently sum(V)=e0 and remainingMass(V)=-e0.

Both inserted p,n and returned x,y are LARGE. Thus G(V)=G(W), U(V)=U(W), and remainingSmall(V)=remainingSmall(W). The exact natural-number identity is H(V)+3^abs(s(x))+3^abs(s(y))=H(W)+3^abs(s(p))+3^abs(s(n)). Native expanding-path energy gives 3^P+3^D<3^r; the returned y term further increases the removed energy. It follows that H(V)<H(W) and J(V)<J(W), with no truncated subtraction or change to the frozen definitions of G,H,U,J.

At a genuine global J minimum over Legal physical words, this exchange contradicts minimality when its stated actual-arrival measurements hold. Deriving both arrival premises from genuine global minimality in Lean remains open, as do availability in the first-Y>P region and full original-quantifier Circle C3.1. Numerical ties remain distinct physical labels. The four-slot escape registration is unfinished under https://github.com/the-omega-institute/trureturing/issues/22063: a faithful complete-telescope source reconstruction, lawful enrolled readout and corresponding whole-family variation, sensitivity and observational-dependence evidence have not been established.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FirstNegativeShiftExchange.actualSource_threeNegative_firstNegative_shift_exchange_full`
- Dependency: [D5/S3/Combinatorics/Circle/ThreeLargePacketExchange](ThreeLargePacketExchange.md)
