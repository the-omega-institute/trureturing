# Refinement Composition Structure

## Abstract

Refinement composes, forms a factorization category, and descends to a preorder.

**Theorem 1.1 (Refinement composition, category laws, and quotient preorder).**

$$\begin{gathered}\forall X, BC, BD, BE: \operatorname{Type},\\{}C: \operatorname{Concept}\left(X, BC\right), D: \operatorname{Concept}\left(X, BD\right), E: \operatorname{Concept}\left(X, BE\right),\\{}(\operatorname{Refines}\left(C, D\right) \Rightarrow \operatorname{Refines}\left(D, E\right) \Rightarrow \operatorname{Refines}\left(C, E\right)) \land\\{}\operatorname{Refines}\left(C, C\right) \land\\{}((\forall r: \operatorname{Readout}\left(X\right), \operatorname{identity}\left(\operatorname{fixedCodomainFactorizationCategory}\left(X\right), r\right) = \operatorname{identityRefinement}\left(\operatorname{readout}\left(r\right)\right)) \land\\{}(\forall r0, r1, r2: \operatorname{Readout}\left(X\right), h0: \operatorname{Refines}\left(\operatorname{readout}\left(r0\right), \operatorname{readout}\left(r1\right)\right), h1: \operatorname{Refines}\left(\operatorname{readout}\left(r1\right), \operatorname{readout}\left(r2\right)\right), \operatorname{compose}\left(\operatorname{fixedCodomainFactorizationCategory}\left(X\right), h0, h1\right) = \operatorname{composeRefinement}\left(h1, h0\right)) \land\\{}(\forall r0, r1: \operatorname{Readout}\left(X\right), h: \operatorname{Refines}\left(\operatorname{readout}\left(r0\right), \operatorname{readout}\left(r1\right)\right), \operatorname{compose}\left(\operatorname{fixedCodomainFactorizationCategory}\left(X\right), \operatorname{identity}\left(\operatorname{fixedCodomainFactorizationCategory}\left(X\right), r0\right), h\right) = h) \land\\{}(\forall r0, r1: \operatorname{Readout}\left(X\right), h: \operatorname{Refines}\left(\operatorname{readout}\left(r0\right), \operatorname{readout}\left(r1\right)\right), \operatorname{compose}\left(\operatorname{fixedCodomainFactorizationCategory}\left(X\right), h, \operatorname{identity}\left(\operatorname{fixedCodomainFactorizationCategory}\left(X\right), r1\right)\right) = h) \land\\{}(\forall r0, r1, r2, r3: \operatorname{Readout}\left(X\right), h0: \operatorname{Refines}\left(\operatorname{readout}\left(r0\right), \operatorname{readout}\left(r1\right)\right), h1: \operatorname{Refines}\left(\operatorname{readout}\left(r1\right), \operatorname{readout}\left(r2\right)\right), h2: \operatorname{Refines}\left(\operatorname{readout}\left(r2\right), \operatorname{readout}\left(r3\right)\right), \operatorname{compose}\left(\operatorname{fixedCodomainFactorizationCategory}\left(X\right), \operatorname{compose}\left(\operatorname{fixedCodomainFactorizationCategory}\left(X\right), h0, h1\right), h2\right) = \operatorname{compose}\left(\operatorname{fixedCodomainFactorizationCategory}\left(X\right), h0, \operatorname{compose}\left(\operatorname{fixedCodomainFactorizationCategory}\left(X\right), h1, h2\right)\right))) \land\\{}((\forall A, B: \operatorname{Readout}\left(X\right), \operatorname{toAntisymmetrization}\left((P, Q: \operatorname{Readout}\left(X\right) \mapsto P \leq Q), A\right) \leq \operatorname{toAntisymmetrization}\left((P, Q: \operatorname{Readout}\left(X\right) \mapsto P \leq Q), B\right) \iff \operatorname{Refines}\left(\operatorname{readout}\left(A\right), \operatorname{readout}\left(B\right)\right)) \land\\{}(\forall left: \operatorname{ReadoutRefinementClass}\left(X\right), left \leq left) \land\\{}(\forall left, middle, right: \operatorname{ReadoutRefinementClass}\left(X\right), left \leq middle \Rightarrow middle \leq right \Rightarrow left \leq right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementFactorization/RefinementCompositionStructure.refinement_composition_category_and_quotient_preorder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Canonical refinement is factorization of one concept readout through another. Existing family theorems supply transitivity by composition and reflexivity by the identity map.

The named factorization-category object uses those source maps as its morphisms. The public statement exposes its identity and composition computations together with both unit laws and associativity.

All bundled concept readouts are quotiented by mutual refinement through Mathlib antisymmetrization. The quotient order is identified publicly with refinement of representatives and is then stated directly to be reflexive and transitive.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementFactorization/RefinementCompositionStructure.refinement_composition_category_and_quotient_preorder`
- Dependency: [D5/S3/ConceptDynamics/Refinement/RefinementReflexivity](../Refinement/RefinementReflexivity.md)
- Dependency: [D5/S3/ConceptDynamics/Refinement/RefinementTransitivity](../Refinement/RefinementTransitivity.md)
- Dependency: [D5/S3/ObserverMemory/Refinement/FactorizationCategory](../../ObserverMemory/Refinement/FactorizationCategory.md)
