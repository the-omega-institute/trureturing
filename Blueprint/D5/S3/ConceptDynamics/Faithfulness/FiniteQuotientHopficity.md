# Malcev Hopficity through finite quotients

## Abstract

Finitely generated residually finite groups are Hopfian.

**Theorem 1.1 (Surjective endomorphisms are injective).**

$$\forall u \in UniverseLevel,\; \forall G \in Type\left(u\right),\; \forall instGroup \in \operatorname{Group}\left(G\right),\; \forall instFG \in Group.FG\left(G\right),\; \forall instRF \in Group.ResiduallyFinite\left(G\right),\; \forall f \in \operatorname{MonoidHom}\left(G, G\right),\; Function.Surjective\left(f\right) \Rightarrow Function.Injective\left(f\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Faithfulness/FiniteQuotientHopficity.surjective_endomorphism_injective` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *Finitely generated residually finite groups are Hopfian*. URL: <https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/GroupTheory/ResiduallyFinite.lean>.

*Commentary.*

For every universe u and every group G in Type u, assume Group.FG G and Group.ResiduallyFinite G. For every monoid homomorphism f from G to itself, Function.Surjective f implies Function.Injective f: for arbitrary x and y in G, equality of f(x) and f(y) forces x = y. G may be infinite and noncommutative; neither a countability assumption nor a decidability assumption is imposed.

Fix a finite quotient Q of G. Finite generation supplies a finite generating set, and a homomorphism G to Q is determined by its values on that set. Thus the type of these homomorphisms is finite. The finite-hom argument allows independent universes for its source and target and only requires MulOneClass, IsMulFG on the source, and Finite on the target.

Precomposition with a surjective f is injective on the homomorphisms G to Q, hence surjective on this finite type. Consequently the quotient map factors as psi composed with f. If f(x) = 1, every such quotient map sends x to 1. Residual finiteness separates each nonidentity element from 1 in some finite quotient, so the kernel of f is trivial and f is injective.

The joint finite-quotient kernel result identifies residual finiteness with joint faithfulness of all finite-quotient observations. Here finite generation additionally makes each homomorphism type finite, enabling the factorization argument. No fixed finite observation budget or coherent inverse system is required. The theorem supplies no executable inverse, complexity bound, or physical realization guarantee. Applying it to a finitely generated free group requires a separate residual-finiteness result.

The mathematical source is the Tau Ceti contributors' Group.ResiduallyFinite.injective_of_surjective and its finite-hom instance at the immutable revision identified in the Library note. This is the classical Malcev theorem. The source code attests the exact formal statement; its citation of Malcev's article is not a primary-text attestation.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/FiniteQuotientHopficity.surjective_endomorphism_injective`
