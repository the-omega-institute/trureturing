# Full native three-negative physical exchange

## Abstract

Full native three-negative exchange on physical labels with an arbitrary signed prefix.

Let k,t be natural numbers with k>=3. The actual centered source is f=s(k,t) on all physical Fin(k) labels, with n=hit(k,1,p), x=hit(k,2,p), N=2^k-1, Q=2^(k-2), and C=2Q-1. Take actual p,y,zpen,z and finite physical lists A,T0,T1,T2,E. Put W=A++[x]++T0++[y]++T1++[zpen]++T2++[z]++E. Assume f(p)>0, Q<=|f(n)|, N<3|f(p)|, Legal W, p and n absent from the entire W, every entry of T0++T1++T2++E SMALL, and Q<=-f(y), Q<=-f(zpen), Q<=-f(z). A is arbitrary signed. Legal includes physical Nodup and the strip bounds 0<=mass(f,W.take(m))<=C for every natural m, including zero and takes beyond the list length.

**Theorem 1.1 (A Legal strict-J competitor always exists).**

Lean statement: `D5/S3/Combinatorics/Circle/ThreeNegativeExchange.actualSource_threeNegative_exchange_full`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ThreeNegativeExchange.actualSource_threeNegative_exchange_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exists an actual finite physical list V with Legal V and J(V)<J(W). Here J is the lexicographic objective (G,H,U): G counts unused LARGE labels, H sums 3^|f(a)| over used LARGE labels, and U counts all unused labels. The conclusion has no minimum, selector, unused SMALL resource, parent status, overshoot or endpoint assumption. Numerical ties and proper numerical periods remain allowed.

Suppose no strict competitor exists. Linear order then gives J(W)<=J(V) for every Legal V of every length. This exact all-length inequality is used internally. Write P=f(p), D=|f(n)|, B=C-P, d=P-D, Y=-f(y), Zpen=-f(zpen), Z=-f(z), L=A++[x]++T0, R=L++[y]++T1++[zpen], F=R++T2, s0=mass(f,L), w=mass(f,R), and u=mass(f,F). Native geometry gives f(n)=-D, D=2B+1, Q<=D<P, d>0, d<=B, and C-d=B+D. TerminalSmallOwnership.actualSource_terminal_small_ownership_prefix applied to F,z,E gives C-d<u and B<q(m)<D for q(m)=mass(f,F++[z]++E.take(m)), for every natural m.

If Y<=P, the terminal corridor at the saturated take supplies B<mass(f,W)<D. FirstNegativeShiftExchange.actualSource_threeNegative_firstNegative_arrival_free_exchange_full then gives an actual Legal strict-J competitor from the original source hypotheses. No extra arrival assumption is introduced.

Assume P<Y. Original legality gives Y<=s0<=C and 0<=w<=C-Zpen<=Q-1. If w<=B, the literal cut R++[p,n] returns T2++[z]++E. Two LARGE insertions replace only one returned LARGE, so G strictly decreases. Thus B<w<Q and Zpen<P. If D<Z, replace only the terminal z by the whole-word fresh n, retaining E in its original order. Every new E-prefix has height q(m)+Z-D in (0,Z), hence in [0,C]. Its one-for-one LARGE inventory preserves G and U and strictly lowers H. Therefore Q<=Z<=D.

Set ell=D-w. Integrality gives 1<=ell<=B, while mass(T2)=u-w>ell. Removing nonpositive entries cannot decrease mass. If no actual positive entry of T2 reaches ell, PositiveSmallReturnExchange.first_crossing chooses a physical sublist S of the positive filter with ell<=mass(S)<=2ell-2. Its prefixes are monotone and Legal after R. The endpoint lies in [D,C-d], where appending fresh [n,p] returns only z among the LARGE labels and strictly lowers G. Hence some actual v in T2 has 0<V=f(v)<Q and ell<=V. The literal R++[v] is Nodup and Legal. Applying the same pair cut whenever w+V<=C-d forces w+V>C-d. This inference uses neither an unused SMALL label nor an inverse parent.

Define beta=s0-Zpen and delta=D-V. Then 0<beta<Q and 0<delta<B. If beta<=B, use V1=L++[zpen,p,n]. The new heights after the unchanged literal L are beta, beta+P, beta+d, all in [0,C]. Return [y]++T1++T2++[z]++E and insert exactly [p,n].

Otherwise beta>B and alpha=beta-delta satisfies 0<alpha<Q. The physical packet L++[n,v,zpen] has new heights s0-D, s0-delta, alpha. These are legal since s0>=Y>P>D and delta>0. If alpha<=B, append p to obtain V2=L++[n,v,zpen,p], whose final height alpha+P is at most C. Return y,z,T1,T2 with the single physical v erased, and E; insert [p,n].

In the remaining case B<alpha<Q, let T=T1++(T2.erase(v)) and ell2=Z-alpha. Then 1<=ell2<=B, and alpha+mass(T)=u+Y-D>Z. The actual positive filter of T has sufficient mass. If one entry reaches ell2, select that physical singleton; otherwise use the owned first-crossing scan to select Sel with ell2<=mass(Sel)<=2ell2-2. In the singleton case alpha+mass(Sel)<=2Q-2<C. In the short-entry case alpha+mass(Sel)<=Z+ell2-2<=D+B-2<C. Positivity controls every intermediate prefix. Thus V3=L++[n,v,zpen]++Sel++[z] is Legal: the height before z lies in [Z,C], and its final height is nonnegative. Return only y among the LARGE labels and all unselected SMALL occurrences; insert only n.

Each selected list is an actual physical sublist; its complementary list is supplied by a permutation of the original available batch. All constructions have a checked total physical permutation (V++Ret).Perm(W++I), with I consisting only of whole-word fresh LARGE labels. The original Nodup word, opposite signs of p,n, and erasure of the single actual v prove that no physical occurrence is used twice. TwoOppositeLargeExchange.inventory_of_perm gives both physical partitions and the direct balances G(V)+largeUsed(I)=G(W)+largeUsed(Ret), H(V)+H(Ret)=H(W)+H(I), and U(V)+I.length=U(W)+Ret.length. Total source mass zero is used only for the full physical source in this inventory, never for a proper subset.

Cases V1 and V2 return y,z among the LARGE labels and insert p,n, preserving G. Since D<P<Y, the owned power threshold gives 3^P+3^D<3^Y+3^Z, so H strictly decreases. Case V3 returns y and inserts n, again preserving G, while 3^D<3^Y gives strict H descent. The objective comparison is independent of U. Every prefix inside literal L, including all signed entries of A, is inherited. InStrip controls every appended endpoint and every positive selected prefix; saturated natural takes keep the checked final endpoint. Each case contradicts the exact all-length inequality and proves the original existential exchange.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/ThreeNegativeExchange.actualSource_threeNegative_exchange_full`
- Dependency: [D5/S3/Combinatorics/Circle/OddFirstNegativePlacement](OddFirstNegativePlacement.md)
- Dependency: [D5/S3/Combinatorics/Circle/TerminalSmallOwnership](TerminalSmallOwnership.md)
