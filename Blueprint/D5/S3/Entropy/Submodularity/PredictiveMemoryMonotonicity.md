# Predictive Memory Monotonicity

## Abstract

Predictive memory is monotone under deterministic readout refinement.

**Theorem 1.1 (Refinement cannot increase residual predictive memory).**

$$\begin{gathered}\forall P, F, Fine, Coarse,\\{}[\operatorname{Fintype}(P)] [\operatorname{Fintype}(F)] [\operatorname{Fintype}(Fine)] [\operatorname{Fintype}(Coarse)],\\{}p: P \times F \to \mathbb{R},\\{}(\forall z, 0 \leq p(z)) \land \sum_{z} p(z) = 1 \Rightarrow\\{}\forall qf: P \to Fine, qc: P \to Coarse,\\{}\operatorname{Refines}(qc, qf) \Rightarrow\\{}\operatorname{predictiveMemory}(p, qf) \leq \operatorname{predictiveMemory}(p, qc).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Submodularity/PredictiveMemoryMonotonicity.predictive_memory_monotone_under_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be a normalized nonnegative joint mass function on a finite past P and future F. Let qf and qc be deterministic readouts of the same past into finite fine and coarse carriers.

The canonical refinement premise says that qc factors through qf. Thus the coarse readout is obtained from the fine one by a deterministic forgetting map.

The imported refinement decomposition identifies the coarse-minus-fine predictive memory with a nonnegative conditional-information gain. The displayed inequality is its direct monotonicity consequence.

## References

- Truth anchor: `D5/S3/Entropy/Submodularity/PredictiveMemoryMonotonicity.predictive_memory_monotone_under_refinement`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../../ConceptDynamics/ConceptJoinUniversal.md)
- Dependency: [D5/S3/Entropy/Submodularity/RefinementInformationDecomposition](RefinementInformationDecomposition.md)
