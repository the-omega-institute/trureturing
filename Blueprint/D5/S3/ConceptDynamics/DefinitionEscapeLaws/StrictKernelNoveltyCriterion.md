# Strict Kernel Novelty Criterion

## Abstract

Strict kernel shrinkage is exactly semantic novelty of the added readout.

**Theorem 1.1 (A readout is novel exactly when it splits an old kernel pair).**

$$\begin{gathered}\forall X, O: \operatorname{Type},\\{}\Gamma: \operatorname{Set}(\operatorname{Concept}(X, O)), p: \operatorname{Concept}(X, O),\\{}\operatorname{StrictSubset}(\operatorname{jointKernel}(\lambda d: \operatorname{insert}(p, \Gamma), \operatorname{readout}(d)), \operatorname{jointKernel}(\lambda d: \Gamma, \operatorname{readout}(d))) \Leftrightarrow\\{}\neg(p \in \operatorname{SemanticClosure}(\Gamma)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeLaws/StrictKernelNoveltyCriterion.strict_kernel_novelty_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Gamma is an output-valued concept family on X, and p is a candidate concept on the same carrier. SemanticClosure and jointKernel are the canonical imported objects.

The inserted-family kernel is always contained in the original kernel. The frozen zero-gain criterion identifies equality with closure membership, so inequality is exactly strict shrinkage.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeLaws/StrictKernelNoveltyCriterion.strict_kernel_novelty_criterion`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeLaws/SemanticClosureZeroGainCriterion](SemanticClosureZeroGainCriterion.md)
