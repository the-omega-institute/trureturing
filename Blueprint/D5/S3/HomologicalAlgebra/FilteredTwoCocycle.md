# Lifting two-cocycle primitives

## Abstract

Native two-cocycle primitives lift through equivariant short exact sequences and finite stable filtrations.

**Theorem 1.1 (An actual equivariant short exact sequence).**

$$\forall (R: Type) (G: Type) (A: Type) (B: Type) (C: Type) [\operatorname{CommRing}\left(R\right)] [\operatorname{Group}\left(G\right)] [\operatorname{AddCommGroup}\left(A\right)] [\operatorname{Module}\left(R, A\right)] [\operatorname{AddCommGroup}\left(B\right)] [\operatorname{Module}\left(R, B\right)] [\operatorname{AddCommGroup}\left(C\right)] [\operatorname{Module}\left(R, C\right)] , \forall (a: \operatorname{Representation}\left(R, G, A\right)), \forall (b: \operatorname{Representation}\left(R, G, B\right)), \forall (c: \operatorname{Representation}\left(R, G, C\right)), \forall (i: \operatorname{IntertwiningMap}\left(a, b\right)), \forall (q: \operatorname{IntertwiningMap}\left(b, c\right)), {\operatorname{Injective}\left(i\right)} \Rightarrow {\operatorname{Surjective}\left(q\right)} \Rightarrow {\operatorname{range}\left(i\right)=\operatorname{ker}\left(q\right)} \Rightarrow {\operatorname{Htwo}\left(a\right)} \Rightarrow {\operatorname{Htwo}\left(c\right)} \Rightarrow \operatorname{Htwo}\left(b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FilteredTwoCocycle.all_two_cocycles_are_coboundaries_of_short_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient ring R is any commutative ring, G any group, and A, B and C arbitrary R-modules in independent universes. The maps i and q are native Representation.IntertwiningMap values. Their range and kernel are those of their underlying linear maps. Htwo(rho) abbreviates AllTwoCocyclesAreCoboundaries rho: every native raw groupCohomology.IsCocycle₂ for precisely the action rho has a native IsCoboundary₂ primitive.

Project a B-valued cocycle f to C and obtain its one-cochain primitive c. Choose a pointwise lift b of c through q. The residual f minus d(b) has values in the kernel of q. Exactness lifts this residual to A; injectivity of i transfers the cocycle identity to that lift. An A-valued primitive a then gives the B-valued primitive b plus i(a). No linear or equivariant section of q is assumed.

This is a direct cochain construction of the familiar exact-sequence vanishing implication. The construction uses Mathlib's raw low-degree predicates and intertwining maps; no literature novelty is claimed.

**Theorem 1.2 (The actual successive quotients suffice).**

$$\forall (R: Type) (G: Type) (M: Type) [\operatorname{CommRing}\left(R\right)] [\operatorname{Group}\left(G\right)] [\operatorname{AddCommGroup}\left(M\right)] [\operatorname{Module}\left(R, M\right)] , \forall (r: \operatorname{Representation}\left(R, G, M\right)), \forall (F: Nat\to \operatorname{Subrepresentation}\left(r\right)), {\operatorname{Monotone}\left(F\right)} \Rightarrow \forall (n: Nat), {\operatorname{F}\left(0\right)=\operatorname{bot}\left(\right)} \Rightarrow {\operatorname{F}\left(n\right)=\operatorname{top}\left(\right)} \Rightarrow {\forall (k: Nat), {k<n} \Rightarrow \operatorname{Htwo}\left(\operatorname{Grade}\left(F, k\right)\right)} \Rightarrow \forall (f: (G\times G)\to M), {\operatorname{Coc}\left(r, f\right)} \Rightarrow \operatorname{Bound}\left(r, f\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FilteredTwoCocycle.is_coboundary_two_of_finite_stable_filtration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In this formula, Coc(rho,f) and Bound(rho,f) are the native raw cocycle and coboundary predicates with SMul g x defined by rho g x. Thus Coc means f(gh,j) plus f(g,h) equals rho(g)f(h,j) plus f(g,hj), and Bound means there exists b with rho(g)b(h) minus b(gh) plus b(g) equal to f(g,h) for every g and h.

Write Step(F,k) for filtrationStep F k, the inverse image of F k under the native subtype of F(k+1). Grade(F,k) is filtrationGrade F k: the quotient representation of F(k+1) by Step(F,k), on the actual Submodule.Quotient carrier. Monotonicity identifies the range of F k inclusion with Step(F,k), while the kernel of the quotient map is exactly this submodule.

Induction starts at the zero subrepresentation and applies the equivariant short exact construction at each successive quotient. At F n equal to top, the resulting primitive maps to the original ambient module. The filtration length may be zero. Neither G nor the coefficient module needs to be finite; no dimension, semisimplicity or split-filtration condition is imposed.

FilteredExtensionSplitting uses this primitive on the actual factor cocycle of a group extension. Separate trace-one operators on the native grades supply the graded hypotheses in its finite-group specialization. The filtration theorem neither assumes nor constructs a trace-one operator on the ambient coefficients.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/FilteredTwoCocycle.all_two_cocycles_are_coboundaries_of_short_exact`
- Truth anchor: `D5/S3/HomologicalAlgebra/FilteredTwoCocycle.is_coboundary_two_of_finite_stable_filtration`
