# Semantic Closure Zero-Gain Criterion

## Abstract

Semantic closure is exactly preservation of the common observational kernel.

**Theorem 1.1 (A candidate has zero gain exactly when the common kernel is unchanged).**

$$\begin{gathered}\forall X, O: \operatorname{Type},\\{}\Gamma: \operatorname{Set}(\operatorname{Concept}(X, O)), p: \operatorname{Concept}(X, O),\\{}p \in \operatorname{SemanticClosure}(\Gamma) \Leftrightarrow\\{}\operatorname{jointKernel}(\lambda d: \operatorname{insert}(p, \Gamma), \operatorname{readout}(d)) = \operatorname{jointKernel}(\lambda d: \Gamma, \operatorname{readout}(d)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeLaws/SemanticClosureZeroGainCriterion.semantic_closure_zero_gain_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Gamma is a family of output-valued concepts on X, and p is a candidate concept on the same carrier. SemanticClosure and jointKernel are imported from the canonical definition-kernel family.

If p is constant on Gamma's common kernel, the extra inserted coordinate cannot split any old kernel pair. Conversely, equality of the inserted and old kernels forces p to agree on every old kernel pair.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeLaws/SemanticClosureZeroGainCriterion.semantic_closure_zero_gain_criterion`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois](../DefinitionEscape/DefinitionKernelGalois.md)
