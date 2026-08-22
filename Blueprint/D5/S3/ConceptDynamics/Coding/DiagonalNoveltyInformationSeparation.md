# Diagonal Novelty and World Information

## Abstract

Diagonal catalog escape need not strictly refine world-state information.

**Theorem 1.1 (Representational novelty need not add world information).**

$$\forall A, Y, X, B_{C}, B_{E}: \operatorname{Type},\\{}f: Y \to Y, g: A \to A \to Y,\\{}C: X \to B_{C}, Sem: (A \to Y) \to X \to B_{E},\\{}{(\forall y, f(y) \neq y) \Rightarrow \neg {\operatorname{diagonal}(f, g) \in \operatorname{range}(g)}} \land\\{}{\operatorname{Refines}(Sem(\operatorname{diagonal}(f, g)), C) \Rightarrow \neg \operatorname{StrictRefinement}(C, \operatorname{join}(C, Sem(\operatorname{diagonal}(f, g))))}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/DiagonalNoveltyInformationSeparation.diagonal_novelty_need_not_add_world_information` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The expression address type, symbol type, world-state type, catalog, current world concept, and expression-semantics map are independent source primitives.

The escaped expression is constructed by the canonical twisted diagonal of the supplied catalog. A fixed-point-free twist makes this expression absent from the catalog range.

The second public clause has an independent premise: when the escaped expression's world semantics factors through the current concept, joining that semantic readout to the current concept cannot be a strict refinement.

The first clause applies the frozen qualitative escape theorem. The second applies the frozen concept-join universal property to build the reverse factorization that contradicts strictness.

Neither the expression semantics nor the current concept is defined from the non-strictness goal, so catalog novelty and world information remain distinct carriers.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/DiagonalNoveltyInformationSeparation.diagonal_novelty_need_not_add_world_information`
