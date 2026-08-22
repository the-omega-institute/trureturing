# Predictive Memory under Deterministic Refinement

## Abstract

Predictive memory decomposes exactly across a finer deterministic readout.

**Theorem 1.1 (Deterministic refinement gives an exact nonnegative information gain).**

$$\begin{gathered}\forall P, F, Fine, Coarse,\\{}[\operatorname{Fintype}(P)] [\operatorname{Fintype}(F)] [\operatorname{Fintype}(Fine)] [\operatorname{Fintype}(Coarse)],\\{}p: P \times F \to \mathbb{R},\\{}(\forall z, 0 \leq p(z)) \land \sum_{z} p(z) = 1 \Rightarrow\\{}\forall q: P \to Fine, f: Fine \to Coarse,\\{}(\operatorname{predictiveMemory}(p, f \circ q) - \operatorname{predictiveMemory}(p, q) = \operatorname{refinementGain}(p, q, f)) \land\\{}0 \leq \operatorname{refinementGain}(p, q, f).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Submodularity/RefinementInformationDecomposition.deterministic_refinement_information_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be a normalized nonnegative joint mass function on a finite past P and future F. Let q prime map the past to a finer finite readout, and let f deterministically forget that readout to a coarser one.

The coarse readout is constructed as f composed with q prime. Predictive memory is the imported conditional mutual information between past and future given the named readout. The gain is the conditional mutual information between the fine readout and future given the coarse readout.

The displayed equality and nonnegativity are both public conjuncts. No independence between P and the finer readout is assumed: its law is the deterministic pushforward of the same past/future law.

The proof applies the frozen conditional-information entropy-defect and nonnegativity theorems to the graph-supported induced laws. Exact finite-sum identities identify the coarse law as the pushforward of the fine law.

## References

- Truth anchor: `D5/S3/Entropy/Submodularity/RefinementInformationDecomposition.deterministic_refinement_information_decomposition`
- Dependency: [D5/S3/Entropy/Forgetting/CapacityMonotone](../Forgetting/CapacityMonotone.md)
- Dependency: [D5/S3/Entropy/Submodularity/MutualInformationChainRule](MutualInformationChainRule.md)
