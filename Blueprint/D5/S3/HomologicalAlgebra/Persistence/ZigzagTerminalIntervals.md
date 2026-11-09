# Terminal intervals on the actual oriented path

## Abstract

Finite right-streamlined zigzags split into terminal intervals with their actual right-filtration multiplicities.

**Theorem 1.1 (Streamlined interval decomposition and exact birth counts).**

$$\forall u \in \operatorname{Universe}\left(\right), v \in \operatorname{Universe}\left(\right), K \in \operatorname{Type}\left(u\right), D \in \operatorname{Zigzag}\left(K, v\right), m \in \operatorname{Nat}\left(\right),\; \left(\operatorname{Field}\left(K\right) \land \left(\left(\forall a \in \operatorname{Nat}\left(\right),\; a < m \Rightarrow \operatorname{FiniteDimensional}\left(K, \operatorname{space}\left(D, a\right)\right)\right) \land \left(\forall a \in \operatorname{Nat}\left(\right),\; \operatorname{succ}\left(a\right) < m \Rightarrow \left(\left(\forall f \in \operatorname{LinearMap}\left(K, \operatorname{space}\left(D, a\right), \operatorname{space}\left(D, \operatorname{succ}\left(a\right)\right)\right),\; \operatorname{arrow}\left(D, a\right) = \operatorname{inl}\left(f\right) \Rightarrow \operatorname{Injective}\left(f\right)\right) \land \left(\forall g \in \operatorname{LinearMap}\left(K, \operatorname{space}\left(D, \operatorname{succ}\left(a\right)\right), \operatorname{space}\left(D, a\right)\right),\; \operatorname{arrow}\left(D, a\right) = \operatorname{inr}\left(g\right) \Rightarrow \operatorname{Surjective}\left(g\right)\right)\right)\right)\right)\right) \Rightarrow \left(\left(m = \operatorname{zero}\left(\right) \Rightarrow \operatorname{NonemptyNaturalIso}\left(\operatorname{emptyDiagram}\left(K, u, v\right), \operatorname{emptyIntervalSum}\left(K, u, v\right)\right)\right) \land \left(\forall n \in \operatorname{Nat}\left(\right),\; m = \operatorname{succ}\left(n\right) \Rightarrow \left(\exists r \in \operatorname{Nat}\left(\right), birth \in \operatorname{Fin}\left(r\right) \to \operatorname{Fin}\left(\operatorname{succ}\left(n\right)\right),\; \operatorname{NonemptyNaturalIso}\left(\operatorname{liftedDiagram}\left(D, n, u, v\right), \operatorname{intervalSum}\left(D, n, r, birth, u, v\right)\right) \land \left(\forall i \in \operatorname{Fin}\left(\operatorname{succ}\left(n\right)\right),\; \operatorname{cardBirthFibre}\left(birth, \operatorname{beta}\left(D, n, i\right)\right) = \operatorname{finrank}\left(K, \operatorname{Quotient}\left(\operatorname{R}\left(D, n, \operatorname{succ}\left(i\right)\right), \operatorname{range}\left(\operatorname{inclusion}\left(D, n, i\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Persistence/ZigzagTerminalIntervals.exists_terminal_interval_decomposition` (`✓ std3`). ∎

*Citation.* Gunnar Carlsson; Vin de Silva (2008). *Zigzag Persistence*. URL: <https://arxiv.org/abs/0812.0197v1>.

*Commentary.*

The universes u and v are independent. K is an arbitrary field in Type u, and D is the native Zigzag with vertex modules in Type v and an actual forward or backward linear arrow at every adjacent pair. Only indices below m require finite-dimensional spaces. Every active forward arrow is injective; every active backward arrow is surjective. No basis, barcode, splitting or natural isomorphism is supplied as a hypothesis.

For m=n+1, the source is exactly Paths(Vertex D n), with the original Edge D n. The input is postcomposed with ModuleCat.uliftFunctor into ModuleCat at max u v. terminalInterval D n b uses lifted K at vertices b through n, zero before b, identity on supported generating arrows and zero otherwise. intervalSum is the actual finite categorical biproduct. Fin r records occurrences, so repeated births retain their full multiplicities.

R(D,n,i) below is terminalFiltrationLayer, read from the actual native rightFiltration, including its zero and whole-space endpoints and repeated layers. inclusion(D,n,i) is the proved inclusion from layer i into layer i+1. The quotient is by its actual range inside the next layer. beta(D,n,i) is birthOrder: start with 0, append the new vertex at a forward arrow and prepend it at a backward arrow. Every factor dimension, including zero, equals the corresponding occurrence count. cardBirthFibre(birth,b) is the cardinality of the subtype of j in Fin r with birth j=b.

The construction extends compatible coordinates through an injective arrow using a complement of its image, and through a surjective arrow using a linear section and its kernel. Existing Mathlib complement, section and finite-basis APIs provide these ingredients. Generating-arrow squares extend to all actual paths; pointwise linear equivalences give the natural isomorphism. Rank-nullity and the proved quotient-dimension formula connect the native filtration recurrence to the birth fibres. ZigzagNaturalLift provides the native data, filtration and source-category interfaces; its endomorphism reconstruction is not repeated.

At m=0, EmptyVertex has no objects, and the conclusion is an actual natural isomorphism from its unique diagram to the empty biproduct. Native n=0 instead means one vertex. All-zero spaces, repeated intervals, arbitrary characteristic and every direction word remain in scope; inactive tail data are unconstrained. The result asserts existence, without canonical choices or a unique isomorphism. Early-death intervals and unrestricted type-A classification are outside this statement.

The positive-length specification is Carlsson and de Silva, Zigzag Persistence, arXiv:0812.0197v1, Theorem 3.19 in Section 3, with the birth ordering of Definition 3.6. Paper vertices 1 through m correspond to native vertices 0 through m-1. The empty source is the explicit vacuous extension. This is a formalization of a known theorem, without a claim of mathematical novelty or an open-problem resolution.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/ZigzagTerminalIntervals.exists_terminal_interval_decomposition`
- Dependency: [D5/S3/HomologicalAlgebra/Persistence/ZigzagNaturalLift](ZigzagNaturalLift.md)
