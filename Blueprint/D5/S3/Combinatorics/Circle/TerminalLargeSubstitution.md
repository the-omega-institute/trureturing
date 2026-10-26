# Same-sign substitution with a compatible suffix

## Abstract

Replace an actual LARGE label by a strictly smaller unused LARGE label of the same sign, deriving the new endpoint from old append blocking and retaining its entire compatible physical suffix.

The original append failure forces the new endpoint to lie in the strip. Pairwise compatible opposite suffix steps can then be ordered between the derived endpoints, retaining every suffix label while strictly lowering the consumed LARGE energy. The terminal all-SMALL result is a specialization.

**Theorem 1.1 (Strict physical substitution with the forced endpoint).**

Lean statement: `D5/S3/Combinatorics/Circle/TerminalLargeSubstitution.actualSource_terminal_sameSign_substitution_full`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/TerminalLargeSubstitution.actualSource_terminal_sameSign_substitution_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact native telescope: k>=3, t natural, physical A,T,z,u, actual source s=actualSource(k,t), C=(2^k-1)/2 and Q=2^(k-2). W=A++[z]++T is Legal, all T labels satisfy |s|<Q, u is unused in the entire W, Q<=|s(u)|, 0<s(u)*s(z), |s(u)|<|s(z)|, and appending u to the ORIGINAL W fails Legal. The old LARGE status of z follows from the strict magnitude comparison and is not an extra premise. There is no minimum assumption, source-profile callback, assumed new endpoint or prelegal competitor.

Output E.Perm(T) and the literal V=A++[u]++E. Put a=sum(A), h=sum(W), D=|s(u)|, Z=|s(z)|, b=a+s(u), e=h-s(z)+s(u). In the negative case old a>=Z gates b=a-D, while old blocking gives h<D. Thus e=h+Z-D>=0 and e<Z<=C. In the positive case old a+Z<=C gates b=a+D, while blocking gives h>C-D. Hence e=h-Z+D<=C and e>C-Z>=0. All these gates and endpoints are proved from the actual hypotheses.

For SMALL T, every opposite pair has combined magnitude at most 2Q-2<C=2Q-1. SmallStepOrdering.exists_order_between, with the actual weights and the proved b,e, therefore permutes ALL T between these endpoints. The original physical prefix A is unchanged. Appending the checked singleton u and the full SMALL order proves original-zero-start InStrip and all natural take bounds, including zero and overlength takes. Zero SMALL values are allowed.

The total-word permutation (V++[z]).Perm(W++[u]), original Nodup and unused u prove V.Nodup and exact disjoint physical partitions Snew=(Sold minus {z}) union {u} and Rnew=(Rold minus {u}) union {z}. The complement sum is exactly -sum(V). The endpoint identity sum(V)=sum(W)-s(z)+s(u) is exported. No same-consumed-set transport is used, and equal-valued physical labels are never identified.

Reuse G,H,U,J from MixedSuffixEnergy. The exact balances give Gnew=Gold, Unew=Uold, and Hnew+3^Z=Hold+3^D. Strict D<Z yields 3^D<3^Z, so Hnew<Hold and Jnew<Jold for priority (G,H,U). The unused SMALL set is exactly unchanged. Full C3.1 and universal favorable-path availability remain OPEN; this theorem covers the stated strict terminal substitution only.

**Theorem 1.2 (Strict physical substitution retaining an arbitrary compatible suffix).**

Lean statement: `D5/S3/Combinatorics/Circle/TerminalLargeSubstitution.actualSource_compatibleTail_sameSign_substitution_full`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/TerminalLargeSubstitution.actualSource_compatibleTail_sameSign_substitution_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural k>=3 and t, keep the actual source f=s(k,t), Q=2^(k-2), C=2Q-1 and physical word W=A++[z]++T. Assume W is Legal, u is absent from the WHOLE W, Q<=|f(u)|, 0<f(u)*f(z), |f(u)|<|f(z)|, and appending u to this original W is not Legal. The suffix assumption is exactly: for every physical i,j in T, if f(i)>0>f(j), then f(i)-f(j)<=C. It replaces only the old all-SMALL condition. There is no extra gate, endpoint, injectivity, distinctness, minimum or competitor premise.

Write a=sum(A), h=sum(W), D=|f(u)| and Z=|f(z)|. The actual source bounds give Z<=C and the magnitude comparison makes z LARGE. Old legality gives 0<=a,a+f(z),h<=C. If both signs are negative, a>=Z and failed append gives h<D. Thus b=a-D lies in [0,C] and e=h+Z-D satisfies 0<=e<Z<=C. If both signs are positive, a+Z<=C and failed append gives h>C-D. Thus b=a+D lies in [0,C] and e=h-Z+D satisfies 0<=C-Z<e<=C. These derivations do not use any size or compatibility property of T.

Now e=b+sum(T). Apply SmallStepOrdering.exists_order_between to the actual physical list T, the proved start b, the proved endpoint e and exactly the displayed opposite-pair compatibility. Its proof cannot get stuck: if a positive step would overflow and no negative step fits, their combined magnitudes exceed C, contradicting compatibility; if all remaining steps are nonpositive, the final endpoint bounds every intermediate height. Zero steps are allowed. It returns E.Perm(T) and InStrip(f,C,b,E), retaining all physical occurrences. Append the unchanged legal A, the checked singleton u and this complete order to obtain the literal V=A++[u]++E. The exported bounds quantify over EVERY natural take length, including zero and overlength takes.

Counting physical labels proves (V++[z]).Perm(W++[u]). Reuse inventory_of_perm on original Legal W and whole-word freshness of u to obtain the entire Inventory(k,t,W,V,[u],[z]), including V.Nodup, the exact used and unused disjoint partitions, source and complement balances. This is a physical-label permutation, with no identification of equal-valued labels. The endpoint is exactly sum(V)=h-f(z)+f(u), and the exported complement identity is remainingMass(f,V)=-(h-f(z)+f(u)). Both inserted and returned labels are LARGE, so the SMALL complement is unchanged.

Inventory gives G(V)=G(W), U(V)=U(W) and H(V)+3^Z=H(W)+3^D. The existing strict exponent comparison for D<Z gives H(V)<H(W), hence strict lexicographic J descent at equal G and U. This is the full physical proof used by the original terminal theorem: its all-SMALL hypothesis supplies compatibility because opposite SMALL magnitudes sum to at most 2Q-2<C.

The parameter boundary is pair compatibility itself, not all-SMALL and not a bound on the number of LARGE suffix labels. A suffix may contain many retained LARGE labels, with arbitrary order and length permitted by the original physical Legal word. In this width C=2Q-1, positive and negative LARGE labels cannot both occur in a compatible suffix, since their magnitudes sum to at least 2Q>C; LARGE labels of one sign are allowed whenever their opposite partners satisfy the exact pair inequality. The conclusion does not claim that every actual suffix is compatible.

Application to the native three-negative configuration: W=A++[x]++T0++[y]++T1++[zpen]++T2++[z]++E, with n=hit(k,1,p), x=hit(k,2,p), f(p)>0, Q<=|f(n)| and N<3|f(p)|. Keep original Legal W, whole-word freshness of p and n, SMALL T0,T1,T2,E, negative LARGE y,zpen,z, and B<h<D, where B=C-f(p), h=sum(W), D=|f(n)|, Zpen=-f(zpen), Z=-f(z). Existing native_geometry gives f(n)=-D; this is derived from the actual source rather than assumed as a scalar profile. Suppose W is a genuine global J minimum among ALL Legal physical words for these fixed k,t: J(W)<=J(V) for every Legal V, without fixing an endpoint or a consumed set.

First, Z>D would permit the original terminal theorem at z with u=n and suffix E. Indeed h<D and f(n)=-D force the appended endpoint h-D<0, so append n is blocked; same sign, freshness and strict magnitude are exactly the other hypotheses. Its Legal witness has J(V)<J(W), contradicting the global minimum. Consequently Z<=D.

Next put R=T2++[z]++E. If Zpen>D and R is compatible, apply the new theorem at zpen with u=n and the unchanged prefix A++[x]++T0++[y]++T1. The same original append n is blocked. It yields a Legal competitor with equal G,U and strictly smaller H,J, again contradicting the global minimum. Here R has only the negative LARGE z outside its SMALL labels. Every opposite SMALL pair already has bound 2Q-2<C, and z cannot be the positive member of a pair. Thus compatibility is equivalent to f(i)+Z<=C for every actual positive SMALL i in T2 or E. At the global minimum one must therefore have Zpen<=D OR an actual positive SMALL i in T2++E with f(i)+Z>C. Since f(i)<=Q-1 and C=2Q-1, any such crossing forces Z>Q. Combined with the terminal exclusion, the honest residual region is Q<Z<=D. This necessary alternative supplies an actual crossing label, not universal compatible-tail availability or a completion of C3.1.

Source context: Damasdi–Frankl–Pach–Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671. These conditional substitutions and their minimum consequence do not settle full C3.1, which remains open.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/TerminalLargeSubstitution.actualSource_compatibleTail_sameSign_substitution_full`
- Truth anchor: `D5/S3/Combinatorics/Circle/TerminalLargeSubstitution.actualSource_terminal_sameSign_substitution_full`
- Dependency: [D5/S3/Combinatorics/Circle/TwoOppositeLargeExchange](TwoOppositeLargeExchange.md)
