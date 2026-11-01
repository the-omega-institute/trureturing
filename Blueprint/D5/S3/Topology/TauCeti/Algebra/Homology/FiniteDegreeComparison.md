# Finite-degree bicomplex comparison

## Abstract

Triangular column homology comparison controls native total homology through a finite degree.

Let C be any abelian category with independent object universe u and morphism universe v. Let K and L be bicomplexes indexed by two natural numbers, with both differentials lowering their respective index. The column p is the actual complex K.X p, and columnMap(phi,p) is phi.f p. Its degree-q homology map is the native homologyMap.

**Theorem 1.1 (Isomorphisms below the boundary and epimorphism on it).**

$$\begin{aligned}\forall C: \operatorname{Type}\left(u\right), [\operatorname{Category}\left(v, C\right)] [\operatorname{Abelian}\left(C\right)] \\\forall k: Nat, \forall K: \operatorname{HomologicalComplex2}\left(C, \operatorname{down}\left(Nat\right), \operatorname{down}\left(Nat\right)\right), \forall L: \operatorname{HomologicalComplex2}\left(C, \operatorname{down}\left(Nat\right), \operatorname{down}\left(Nat\right)\right), \forall phi: \operatorname{Hom}\left(K, L\right), \\(\forall p: Nat, \forall q: Nat, p + q \le k \Rightarrow \operatorname{IsIso}\left(\operatorname{homologyMap}\left(\operatorname{columnMap}\left(phi, p\right), q\right)\right)) \Rightarrow\\(\forall p: Nat, \forall q: Nat, p + q = k + 1 \Rightarrow \operatorname{Epi}\left(\operatorname{homologyMap}\left(\operatorname{columnMap}\left(phi, p\right), q\right)\right)) \Rightarrow\\(\forall n: Nat, n \le k \Rightarrow \operatorname{IsIso}\left(\operatorname{homologyMap}\left(\operatorname{totalMap}\left(phi, \operatorname{down}\left(Nat\right)\right), n\right)\right)) \land \operatorname{Epi}\left(\operatorname{homologyMap}\left(\operatorname{totalMap}\left(phi, \operatorname{down}\left(Nat\right)\right), k + 1\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/TauCeti/Algebra/Homology/FiniteDegreeComparison.finite_degree_comparison_total_map` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (extension-homology support) (2026). *First-quadrant row-to-total quasi-isomorphism comparison*. URL: <https://github.com/TauCetiProject/TauCeti/blob/580580ea8726c50dcf98e199fa0a7caef5a74302/TauCeti/Algebra/Homology/TotalComplex.lean>.

*Commentary.*

Assume the actual column homology map is an isomorphism when p+q is at most k and an epimorphism when p+q=k+1. Then the actual total map is an isomorphism on homology in every degree n at most k and an epimorphism in degree k+1. The boundary epimorphisms are part of the hypotheses and the conclusion. No condition is imposed above that boundary, and no entire row or column is required to be a quasi-isomorphism.

The total object in degree n is the native finite coproduct over p+q=n, and totalMap(phi,down(Nat)) is HomologicalComplex2.total.map on these same coproducts. The differential on the (p,q) summand is d1+(-1)^p d2. Finite antidiagonals supply the needed coproducts in every abelian category. There is no bound on the set of columns or on the support, and no supplied convergence theorem, comparison hypothesis, field or module restriction.

First prove a row version by simultaneous induction on Q: row-homology isomorphisms at p+q<Q and epimorphisms at p+q=Q imply total-homology isomorphisms below Q and an epimorphism at Q. Row zero includes into the total. The quotient is the extension by zero of Tot(rowsSucc(K)) along n mapped to n+1. The short exact sequence splits in each degree, naturally in the bicomplex map. At Q=0 its quotient has zero homology in degree zero, so row-zero surjectivity gives the required epimorphism.

For Q+1, apply the induction hypothesis to rowsSucc, whose row q is the original row q+1. Its triangular bounds are exactly those for Q after reindexing. Extension by zero gives the quotient isomorphisms in degrees below Q+1 and epimorphisms through Q+1, including the preceding degree needed by the middle-map isomorphism lemma. On row zero, the bounded hypotheses supply the isomorphism at the requested degree, the monomorphism in the following degree, and the boundary epimorphism. The local homology-sequence diagram lemmas then give both total assertions. Deleting a row preserves p, so the quotient keeps the sign (-1)^p; this extension is not a signed suspension.

Flip the bicomplex so that its rows are the original columns, with their actual maps phi.f p. The native totalFlipIso identifies the flipped total with the original total by multiplication by (-1)^(p*q) on each summand. Its naturality identifies the total of the flipped morphism with the actual total morphism. Apply the row induction at Q=k+1 and transport homology across this signed isomorphism to obtain precisely the stated column result.

This is a standard general finite-degree comparison theorem. The row-zero decomposition and local transfer statements come from the cited Tau Ceti sources; the bounded induction composes them here. This theorem alone makes no claim about an augmentation, a nerve, an open cover, or a singular-chain construction.

## References

- Truth anchor: `D5/S3/Topology/TauCeti/Algebra/Homology/FiniteDegreeComparison.finite_degree_comparison_total_map`
- Dependency: [D5/S3/Topology/TauCeti/Algebra/Homology/TotalComplex](TotalComplex.md)
