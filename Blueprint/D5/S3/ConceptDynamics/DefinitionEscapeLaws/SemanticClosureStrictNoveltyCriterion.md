# Semantic Closure Strict Novelty Criterion

## Abstract

Strict common-kernel refinement is exactly escape from semantic closure.

**Theorem 1.1 (A candidate is strictly novel exactly when it splits an old kernel pair).**

$$\begin{gathered}\forall X, O: \operatorname{Type},\\{}\Gamma: \operatorname{Set}\left(\operatorname{Concept}\left(X, O\right)\right), p: \operatorname{Concept}\left(X, O\right),\\{}\operatorname{StrictSubset}\left(\operatorname{jointKernel}\left(\lambda d: \operatorname{insert}\left(p, \Gamma\right), \operatorname{readout}\left(d\right)\right), \operatorname{jointKernel}\left(\lambda d: \Gamma, \operatorname{readout}\left(d\right)\right)\right) \Leftrightarrow \neg(p \in \operatorname{SemanticClosure}\left(\Gamma\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeLaws/SemanticClosureStrictNoveltyCriterion.semantic_closure_strict_novelty_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Gamma is an arbitrary family of output-valued concepts on X. The old and extended common kernels are the canonical jointKernel objects, with the candidate inserted into the same family.

The extended kernel is always contained in the old kernel. The inclusion is strict exactly when the frozen zero-gain equality criterion fails, equivalently when the candidate is outside SemanticClosure Gamma.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeLaws/SemanticClosureStrictNoveltyCriterion.semantic_closure_strict_novelty_criterion`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeLaws/SemanticClosureZeroGainCriterion](SemanticClosureZeroGainCriterion.md)
