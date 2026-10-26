# Terminal same-sign substitution

## Abstract

Replace the actual terminal LARGE label by a strictly smaller unused LARGE label of the same sign, deriving the new endpoint from old append blocking and retaining every SMALL label.

The original append failure forces the new endpoint to lie in the strip. Arbitrary-endpoint SMALL ordering then retains every supplied physical SMALL label while strictly lowering the consumed LARGE energy.

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

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/TerminalLargeSubstitution.actualSource_terminal_sameSign_substitution_full`
- Dependency: [D5/S3/Combinatorics/Circle/TwoOppositeLargeExchange](TwoOppositeLargeExchange.md)
