# Late negative reserve and prefix truncation

## Abstract

An actual late negative SMALL reserve can cross the preceding negative LARGE and supply a literal strict G prefix improvement with complete physical inventory.

**Theorem 1.1 (A late actual negative SMALL reserve gives strict G descent).**

Lean statement: `D5/S3/Combinatorics/Circle/LateNegativePrefixExchange.actualSource_late_negative_reserve_prefix_exchange_full`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/LateNegativePrefixExchange.actualSource_late_negative_reserve_prefix_exchange_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The construction uses the general native expanding-pair geometry and the public FirstNegativeShiftExchange.actualSource_prefix_pair_truncation theorem. It is independent of the upper-quarter classifier and applies to an arbitrary signed old prefix and suffix subject only to the stated physical hypotheses.

For arbitrary natural k,t with k>=3, physical labels p,zpen,c:Fin k, arbitrary physical lists F,R and an integer m, put f=s(k,t), Q=2^(k-2), N=4Q-1, C=2Q-1, P=f(p), n=rho(p), D=abs(f(n)) and B=C-P. Assume P>0, Q<=D, N<3*abs(f(p)), the original full W=F++[zpen]++R is Legal from zero, and p,n are unused in all W. The preceding negative LARGE satisfies Q<=-f(zpen). The actual reserve satisfies c in R, f(c)=-m and P-Q<=m<=B. The only suffix resource condition is largeUsed(R)<=1. F may contain arbitrarily many LARGE and arbitrary signed SMALL. R is arbitrary in sign, size and order subject to its LARGE count. These are all hypotheses: there is no endpoint, blocking, global-minimum, Y, parity, quarter, batch, ordering, selector, supplied competitor or additional return-resource premise.

Native geometry proves f(n)=-D, D<P, both inserted labels LARGE and P>Q. Hence P-Q>0, B<Q and 0<m<Q follow from the stated inequalities; c is negative SMALL without an extra positivity assumption. Let Zpen=-f(zpen), a=sum(F++[zpen]) and d1=sum(F). Splitting the ORIGINAL Legal word at F gives d1=a+Zpen, 0<=d1<=C and 0<=a<=C-Zpen<=Q-1. This uses the entire old F, not a numerical suffix or a shifted measurement.

If a<=B, apply the existing prefix-pair truncation to the original prefix F++[zpen] and suffix R. The literal new word is V=F++[zpen,p,n] and Ret=R. Its endpoint is a+P-D. The helper supplies the Legal word and full original-W Inventory directly; its proof is reused.

If B<a, then m<=B<a gives 0<a-m, while m>=P-Q and a<=Q-1 give a-m<=Q-1-m<=2Q-1-P=B. Put literal V=F++[c,zpen,p,n] and Ret=R.erase(c). The four heights after the unchanged F are d1-m, a-m, a-m+P and a-m+P-D. The first equals a-m+Zpen, is positive and is no larger than d1<=C. The next lies in (0,B]. Adding P stays at most C, and subtracting D stays nonnegative because P>D>0. Thus every new gate lies in [0,C]. The old F remains legal from original zero. No ordering theorem or SMALL selector is used, and no old suffix order must survive a translation.

The physical erase permutation R.Perm(c::R.erase(c)), a swap of the actual c past zpen, and a swap of the inserted pair past the return list prove exactly (V++Ret).Perm(W++[p,n]). Original Nodup and whole-W freshness of p,n make this total word Nodup, so Ret is Nodup, every returned label is old in W, and no returned label belongs to V. The existing inventory_of_perm proves the high branch's complete original-W Inventory. That shared engine supplies both exact used and complementary unused disjoint partitions, energy and count balances, source balance, the complement sum and the SMALL partition; no duplicate physical inventory proof is introduced. Physical membership and permutations keep equal-valued labels distinct, including sources with repeated numerical values.

Since c is SMALL, erasing its actual occurrence does not change largeUsed(R). In both branches largeUsed(Ret)=largeUsed(R), and the common exact balance is G(V)+2=G(W)+largeUsed(R). The suffix bound <=1 gives strict G(V)<G(W), hence strict lexicographic J(V)<J(W), without comparing H or U. The theorem exposes the two literal branch alternatives and their endpoint equations, Legal(V), V.Nodup, Ret.Nodup, oldness and absence of every returned occurrence, InStrip from zero, all natural take bounds including zero and overlength, Inventory and the total physical permutation. It also exposes the endpoint bounds, remainingMass(V)=-sum(V), sum(V)+sum(Ret)=sum(W)+P-D, and remainingSmall(V)=remainingSmall(W) union the SMALL returned labels, with this union disjoint. The entire old suffix is returned except c in the high branch; uniform retention of old SMALL is not a conclusion.

For the substantive three-negative application take the actual native W=A++[x]++T0++[y]++T1++[zpen]++T2++[z]++E, where x=rho^2(p), y,zpen,z are negative LARGE, and every entry of T0,T1,T2,E is SMALL. A is arbitrary, including earlier LARGE. Put Y=-f(y)>0 and assume Y mod 4=0. The public negative_parent theorem applied to physical b=rho inverse(y) gives 2f(b)=-Y and b negative SMALL: the odd wrapped alternative is excluded by divisibility. Applied again to the actual c=rho inverse(b), it gives 2f(c)=f(b), hence 4f(c)=-Y and f(c)=-theta with theta=Y/4>0. These are source-cycle equations on the physical inverse labels, not identifications by numerical value. Native 2P<=C+Q=3Q-1 and Y<=C imply theta<=B, since 4theta=Y<=2Q-1 and 2B>=Q-1.

If c lies in T2++E, set F=A++[x]++T0++[y]++T1 and R=T2++[z]++E. Actual membership gives c in R, and small_weights gives largeUsed(R)=1 because z is the sole LARGE there. Whenever theta>=P-Q, equivalently Y>=4(P-Q), the general theorem applies to this exact original source and yields G(V)+1=G(W). It needs neither the original blocking endpoint inequalities nor any last-negative arrival condition. The earlier upper-quarter condition 3Y>4P is sufficient: it gives P<3theta; theta<=P-Q would imply 3Q<2P, contradicting 2P<=3Q-1. Thus upper quarter gives the stronger theta>P-Q and satisfies the general lower bound.

This late-location application gives strict G descent for actual c in either T2 or E, including arbitrary signed T2 and earlier LARGE in A. The previous rich signed-return construction for c in E remains mathematically correct; this application gives a stronger G conclusion there and closes c in T2 by the same literal construction. Combined with the completed earlier c-in-T0/T1 signed construction, the upper-quarter actual-c location obstruction reduces to c in A under the corresponding conditional hypotheses. This does not assert that every physical c is available, does not settle the other parity or quarter regions, and does not prove full Circle C3.1.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/LateNegativePrefixExchange.actualSource_late_negative_reserve_prefix_exchange_full`
- Dependency: [D5/S3/Combinatorics/Circle/FirstNegativeShiftExchange](FirstNegativeShiftExchange.md)
