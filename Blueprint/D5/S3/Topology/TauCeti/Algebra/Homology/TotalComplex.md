# First-quadrant row-to-total comparison

## Abstract

Rowwise quasi-isomorphisms give quasi-isomorphisms of first-quadrant total complexes.

The object universe u and morphism universe v are independent. The coefficient category C is any abelian category. A bicomplex K has objects K(p,q) for natural p and q, with commuting horizontal and vertical differentials lowering their respective indices. Its row q is the horizontal chain complex obtained by evaluating each column at q. A bicomplex morphism phi supplies actual maps of these rows.

**Theorem 1.1 (Comparison of the actual total maps).**

$$\begin{aligned}\forall C: \operatorname{Type}\left(u\right), [\operatorname{Category}\left(v, C\right)] [\operatorname{Abelian}\left(C\right)] \\\forall K: \operatorname{HomologicalComplex2}\left(C, \operatorname{down}\left(Nat\right), \operatorname{down}\left(Nat\right)\right), \forall L: \operatorname{HomologicalComplex2}\left(C, \operatorname{down}\left(Nat\right), \operatorname{down}\left(Nat\right)\right), \forall phi: \operatorname{Hom}\left(K, L\right), \\(\forall q: Nat, \operatorname{QuasiIso}\left(\operatorname{map}\left(\operatorname{mapHomologicalComplex}\left(\operatorname{eval}\left(C, \operatorname{down}\left(Nat\right), q\right), \operatorname{down}\left(Nat\right)\right), phi\right)\right)) \Rightarrow \operatorname{QuasiIso}\left(\operatorname{totalMap}\left(phi, \operatorname{down}\left(Nat\right)\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/TauCeti/Algebra/Homology/TotalComplex.quasiIso_total_map_of_rows` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (extension-homology support) (2026). *First-quadrant row-to-total quasi-isomorphism comparison*. URL: <https://github.com/TauCetiProject/TauCeti/blob/580580ea8726c50dcf98e199fa0a7caef5a74302/TauCeti/Algebra/Homology/TotalComplex.lean>.

*Commentary.*

In degree n, the native total complex is the coproduct of K(p,q) over p+q=n. This antidiagonal is finite, so the finite coproducts already available in an abelian category suffice. On its (p,q) summand the differential is d1 plus (-1)^p times d2. totalMap is the map induced on these same coproducts by phi; it is the native HomologicalComplex2.total.map, with no alternative totalization.

Assume every horizontal row map is a quasi-isomorphism. Then totalMap induces an isomorphism on homology in every natural degree, including zero. There is no bounded-support, bounded-length, exact-infinite-coproduct, AB4, field or module hypothesis. Zero objects and empty antidiagonal summands are included.

Row zero includes as a subcomplex of Tot(K). Delete it and reindex row q+1 as row q to obtain rowsSucc(K). The quotient is the native extension by zero of Tot(rowsSucc(K)) along n mapped to n+1; its object in degree zero is zero. Deleting a row preserves p and therefore preserves the vertical sign (-1)^p. This extension uses the original differential and is not a signed suspension.

Splitting each antidiagonal into its row-zero summand and its positive-row summands gives a degreewise split short exact sequence. These sequences commute with the actual maps induced by phi. Their homology sequences give a simultaneous induction: Tot(phi) induces isomorphisms below Q and an epimorphism in degree Q. At Q=0 the quotient has zero homology in degree zero. For the successor step, apply the preceding bound to the remaining rows and transport homology along extension by zero. The middle-map diagram lemmas then supply both assertions. For any requested degree m, choose Q=m+1 to obtain its homology isomorphism.

This is the relative acyclic assembly statement cited by the Tau Ceti source with a pointer to Weibel, Section 2.7. It supplies the general comparison step for later augmented-row and Cech constructions. It asserts no singular-chain augmentation or descent theorem by itself.

## References

- Truth anchor: `D5/S3/Topology/TauCeti/Algebra/Homology/TotalComplex.quasiIso_total_map_of_rows`
