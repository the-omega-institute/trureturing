# Splitting an Interval from an Actual Finite Diagram

## Abstract

A nonzero finite diagram over any field admits an actual natural interval retraction, vertexwise line/kernel isomorphisms and strict dimension descent.

**Theorem 1.1 (A natural interval and its complementary kernel diagram).**

$$\forall K \in Type, n \in \operatorname{Nat}\left(\right), V \in \operatorname{VertexSpaces}\left(n\right), F \in \operatorname{ModuleCatFunctor}\left(K, V\right),\; \left(\operatorname{Field}\left(K\right) \land \left(\operatorname{FiniteDimensionalVertices}\left(K, V\right) \land \operatorname{NonzeroVertex}\left(V\right)\right)\right) \Rightarrow \left(\exists b \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right), w \in \operatorname{VertexVectors}\left(V\right), p \in \operatorname{VertexFunctionals}\left(K, V\right),\; b \le j \land \left(\operatorname{EarlierZero}\left(V, b\right) \land \left(\operatorname{SupportedNormalized}\left(b, j, w, p\right) \land \left(\operatorname{NaturalVectors}\left(F, b, j, w\right) \land \left(\operatorname{NaturalFunctionals}\left(F, b, j, p\right) \land \left(\operatorname{VertexSplittings}\left(K, V, w, p\right) \land \left(\operatorname{NaturalProjectors}\left(F, w, p\right) \land \left(\operatorname{NaturalKernels}\left(F, p\right) \land \operatorname{StrictDescent}\left(K, V, p\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalSplit.exists_interval_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

K is an arbitrary field. Every V(i) is finite-dimensional, and at least one vertex contains a nonzero vector. There are b <= j, vectors w(i) and functionals p(i). Before b every vertex is zero. Outside b <= i <= j, both w(i) and p(i) vanish; inside, p(i)(w(i))=1.

NaturalVectors means F(i,k)(w(i))=w(k) when b <= i and k <= j, and zero otherwise. NaturalFunctionals means p(k) composed with F(i,k) is p(i) in the same case and zero otherwise. These equations cover arrows entering and leaving the support, not only its interior.

VertexSplittings gives actual linear equivalences from V(i) to span{w(i)} times ker(p(i)), with coordinates p(i)(x) w(i) and x-p(i)(x) w(i). The inverse adds the coordinates. NaturalProjectors says F(i,k) commutes with these projections. NaturalKernels says every arrow maps ker(p(i)) into ker(p(k)). StrictDescent compares the sums of the actual kernel and vertex finranks.

Choose the earliest nonzero vertex and a nonzero vector there, then the last vertex where its forward image survives. Mathlib supplies a scalar linear left inverse at that last vector. Pulling it back along the actual composites gives the functionals. The earliest and last choices prove the boundary squares. Ordinary complement isomorphisms give the displayed splitting; one dimension is removed at every supported vertex, so the total kernel dimension decreases.

The last vertex may lie in the support. No artificial terminal zero is appended. Iterating the construction is the finite-diagram classification step; real-parameter extension, multiset uniqueness and quantitative stability require further arguments.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalSplit.exists_interval_split`
