# Knowledge Refinement Monotonicity

## Abstract

Knowledge by factorization is monotone under indexed readout refinement.

**Theorem 1.1 (Refinement preserves knowledge but coarsening need not).**

$$\begin{gathered}(\forall I, X, T: Type, O: I \to Type,\\{}q: \forall i: I, X \to O(i), P: X \to T,\\{}J, K\in \operatorname{Finset}(I), J \subseteq K \Rightarrow (\operatorname{Refines}(P, \operatorname{jointReadout}(\operatorname{restrict}(q, J))) \Rightarrow \operatorname{Refines}(P, \operatorname{jointReadout}(\operatorname{restrict}(q, K)))))\\{}\land\\{}(\exists q: Unit \to (Bool \to Bool), P: Bool \to Bool,\\{}J, K\in \operatorname{Finset}(Unit), J \subseteq K\\{}\land\\{}\operatorname{Refines}(P, \operatorname{jointReadout}(\operatorname{restrict}(q, K)))\\{}\land\\{}\neg \operatorname{Refines}(P, \operatorname{jointReadout}(\operatorname{restrict}(q, J)))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/EpistemicRefinement/KnowledgeRefinementMonotonicity.knowledge_monotone_under_indexed_refinement_with_converse_countermodel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Knowledge is displayed directly as factorization of the target through the canonical joint readout. For nested finite budgets, restriction from the fine joint output to the coarse output supplies the readout refinement.

Composing the coarse target factor with that restriction proves the first public clause for arbitrary state, output, and target carriers. No separate knowledge predicate or joint-readout construction is declared.

The second public clause is a shared countermodel: one Boolean target, one indexed Boolean readout, and nested budgets jointly witness fine knowledge and the absence of coarse knowledge. Its positive and negative parts therefore cannot be separated into unrelated constructions.

## References

- Truth anchor: `D5/S3/ConceptDynamics/EpistemicRefinement/KnowledgeRefinementMonotonicity.knowledge_monotone_under_indexed_refinement_with_converse_countermodel`
- Dependency: [D5/S3/ConceptDynamics/Refinement/RefinementTransitivity](../Refinement/RefinementTransitivity.md)
- Dependency: [D5/S3/ConceptDynamics/RefinementFactorization/IndexedReadoutMonotonicity](../RefinementFactorization/IndexedReadoutMonotonicity.md)
