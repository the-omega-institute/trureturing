# Neighborhood-cover gluing and the ordinary Cech colimit

## Abstract

Strict functors on an arbitrary neighborhood cover glue uniquely, and the ordinary finite-intersection open Cech cocone is a colimit in groupoids.

**Theorem 1.1 (Strict extension from an arbitrary neighborhood cover).**

$$\forall (X: Type\left(u\right)), [TopologicalSpace\left(X\right)] \forall (I: Type\left(v\right)), \forall (z: UniverseLevel), \forall (D: Type\left(w\right)), [Category\left(z, D\right)] \forall (U: I \to Set\left(X\right)), \forall (F: (\forall (i: I), Functor\left(FundamentalGroupoid\left(U\left(i\right)\right), D\right))), (\forall (x: X), \exists (i: I), U\left(i\right) \in nhds\left(x\right)) \Rightarrow \left((\forall (i: I), \forall (j: I), comp\left(map\left(inclusion\left(inter\left(U\left(i\right), U\left(j\right)\right), U\left(i\right)\right)\right), F\left(i\right)\right) = comp\left(map\left(inclusion\left(inter\left(U\left(i\right), U\left(j\right)\right), U\left(j\right)\right)\right), F\left(j\right)\right)) \Rightarrow \exists! (G: Functor\left(FundamentalGroupoid\left(X\right), D\right)), \forall (i: I), comp\left(map\left(subtypeVal\left(U\left(i\right)\right)\right), G\right) = F\left(i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/TauCeti/AlgebraicTopology/FundamentalGroupoid/NeighborhoodCover.existsUnique_extension` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kim Morrison; Lean FRO, LLC (2026). *Fundamental-groupoid gluing for arbitrary neighborhood covers*. URL: <https://github.com/TauCetiProject/TauCeti/blob/3780371ca1bebf9f1c2bb3d753e4bb56c9526023/TauCeti/AlgebraicTopology/FundamentalGroupoid/Glue.lean>.

*Commentary.*

For every topological space X, every index type I and every family U of subsets of X whose members are neighborhoods pointwise, and every target category D, compatible functors on the subtype fundamental groupoids of the U(i) have a unique strict extension to the fundamental groupoid of X. The cover members need not be open, intersections may be empty, and no connectedness, finiteness, basepoint or nonempty-intersection premise is added.

**Definition 1.2 (The ordinary finite-intersection Cech cocone).**

$$\forall (X: TopCat\left(v\right)), \forall (I: Type\left(u\right)), \forall (U: I \to Opens\left(X\right)), IsOpenCover\left(U\right) \Rightarrow IsColimit\left(cechCocone\left(U\right)\right)$$

*Formalization.* `D5/S3/Topology/TauCeti/AlgebraicTopology/FundamentalGroupoid/NeighborhoodCover.isColimitCechCocone` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Kim Morrison; Lean FRO, LLC (2026). *Fundamental-groupoid gluing for arbitrary neighborhood covers*. URL: <https://github.com/TauCetiProject/TauCeti/blob/3780371ca1bebf9f1c2bb3d753e4bb56c9526023/TauCeti/AlgebraicTopology/FundamentalGroupoid/Glue.lean>.

*Commentary.*

For an arbitrary open cover, the diagram is indexed by nonempty finite subsets ordered by reverse inclusion. Its objects are the fundamental groupoids of the corresponding intersections, with geometric empty intersections retained by the diagram. The displayed cocone is an ordinary IsColimit in Grpd; no pseudocolimit or natural-isomorphism replacement is asserted.

**Definition 1.3 (Fundamental-groupoid Cech diagram).**

Lean statement: `D5/S3/Topology/TauCeti/AlgebraicTopology/FundamentalGroupoid/NeighborhoodCover.cechDiagram`

*Formalization.* `D5/S3/Topology/TauCeti/AlgebraicTopology/FundamentalGroupoid/NeighborhoodCover.cechDiagram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

cechDiagram is the fundamental-groupoid image of the finite-intersection open diagram.

**Definition 1.4 (Canonical inclusion cocone).**

Lean statement: `D5/S3/Topology/TauCeti/AlgebraicTopology/FundamentalGroupoid/NeighborhoodCover.cechCocone`

*Formalization.* `D5/S3/Topology/TauCeti/AlgebraicTopology/FundamentalGroupoid/NeighborhoodCover.cechCocone` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

cechCocone maps every intersection fundamental groupoid to the full-space fundamental groupoid through its subtype inclusion.

## References

- Truth anchor: `D5/S3/Topology/TauCeti/AlgebraicTopology/FundamentalGroupoid/NeighborhoodCover.cechCocone`
- Truth anchor: `D5/S3/Topology/TauCeti/AlgebraicTopology/FundamentalGroupoid/NeighborhoodCover.cechDiagram`
- Truth anchor: `D5/S3/Topology/TauCeti/AlgebraicTopology/FundamentalGroupoid/NeighborhoodCover.existsUnique_extension`
- Truth anchor: `D5/S3/Topology/TauCeti/AlgebraicTopology/FundamentalGroupoid/NeighborhoodCover.isColimitCechCocone`
