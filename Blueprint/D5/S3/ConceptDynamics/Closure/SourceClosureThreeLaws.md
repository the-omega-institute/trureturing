# Source Closure Three Laws

## Abstract

Source-semantic closure is extensive, monotone, and idempotent.

**Theorem 1.1 (Source closure is extensive, monotone, and idempotent).**

$$\forall X \in Type, O \in Type, S \in \operatorname{Set}\left(\operatorname{Concept}\left(X, O\right)\right), T \in \operatorname{Set}\left(\operatorname{Concept}\left(X, O\right)\right),\; S \subseteq \operatorname{DefinitionClosure}\left(S\right) \land \left(\left(S \subseteq T \Rightarrow \operatorname{DefinitionClosure}\left(S\right) \subseteq \operatorname{DefinitionClosure}\left(T\right)\right) \land \operatorname{DefinitionClosure}\left(\operatorname{DefinitionClosure}\left(S\right)\right) = \operatorname{DefinitionClosure}\left(S\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Closure/SourceClosureThreeLaws.source_closure_three_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

DefinitionClosure is the canonical closure generated from the common kernel of the supplied source concepts; no target-defined closure is introduced.

The three public conjuncts respectively include the generating family, preserve inclusion into a larger family, and make a second closure pass equal to the first.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Closure/SourceClosureThreeLaws.source_closure_three_laws`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois](../DefinitionEscape/DefinitionKernelGalois.md)
