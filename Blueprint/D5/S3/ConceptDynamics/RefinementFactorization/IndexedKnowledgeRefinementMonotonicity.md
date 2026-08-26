# Indexed Knowledge Refinement Monotonicity

## Abstract

Knowledge by factorization is monotone under indexed readout refinement.

**Theorem 1.1 (Refinement preserves knowledge but coarsening need not).**

$$\begin{gathered}(\forall I, X, T: Type, O: I \to Type,\\{}q: \forall i: I, X \to O(i), P: X \to T,\\{}J, K\in \operatorname{Finset}(I), J \subseteq K \Rightarrow (\operatorname{Refines}(P, \operatorname{jointReadout}(\operatorname{restrict}(q, J))) \Rightarrow \operatorname{Refines}(P, \operatorname{jointReadout}(\operatorname{restrict}(q, K)))))\\{}\land\\{}(\exists q: Unit \to (Bool \to Bool), P: Bool \to Bool,\\{}J, K\in \operatorname{Finset}(Unit), J \subseteq K\\{}\land\\{}\operatorname{Refines}(P, \operatorname{jointReadout}(\operatorname{restrict}(q, K)))\\{}\land\\{}\neg \operatorname{Refines}(P, \operatorname{jointReadout}(\operatorname{restrict}(q, J)))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementFactorization/IndexedKnowledgeRefinementMonotonicity.knowledge_monotone_under_indexed_refinement_with_converse_countermodel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Knowledge is target factorization through the canonical joint readout. Restriction from the fine joint output to the coarse output supplies the readout refinement for nested finite budgets.

Composing the coarse target factor with that restriction proves the first public clause for arbitrary state, output, and target carriers.

The second public clause uses one Boolean target, one indexed Boolean readout, and nested budgets as a shared countermodel. The fine budget knows the target while the coarse budget does not.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementFactorization/IndexedKnowledgeRefinementMonotonicity.knowledge_monotone_under_indexed_refinement_with_converse_countermodel`
- Dependency: [D5/S3/ConceptDynamics/EpistemicRefinement/KnowledgeRefinementMonotonicity](../EpistemicRefinement/KnowledgeRefinementMonotonicity.md)
