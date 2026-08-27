# Pareto Frontier Does Not Determine Stop

## Abstract

One Pareto frontier yields opposite stop decisions under two complete sourced orientations.

**Theorem 1.1 (A sourced orientation is necessary to derive the stop target).**

$$\begin{gathered}(\operatorname{NoDominatingCandidate}\left(v_2, D_2\right) \land\\{}\operatorname{AdjudicationStopTargetOnDecisionSet}\left(AdmTarget_2, InScope_2, O_{stay}, D_2\right) \land\\{}\neg \operatorname{AdjudicationStopTargetOnDecisionSet}\left(AdmTarget_2, InScope_2, O_{advance}, D_2\right)) \land\\{}\neg (\operatorname{NoDominatingCandidate}\left(v_2, D_2\right) \Rightarrow \operatorname{AdjudicationStopTargetOnDecisionSet}\left(AdmTarget_2, InScope_2, O_{advance}, D_2\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoFrontierStopDivergence.pareto_frontier_requires_sourced_orientation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is Fin 2. Candidates and feasible actions are both the full carrier, action zero is current, and the five natural-valued coordinates give actions zero and one one strict benefit each.

Both orientations admit every action and keep every action in scope. The stay orientation is equality with false source and version; the advance orientation is index order with true source and version.

The first displayed conjunct is the full three-part finite certificate: no Pareto dominator, a stay-oriented stop, and no advance-oriented stop. The second conjunct separately records the requested failure of implication from the Pareto frontier to the advance stop.

The theorem reuses the frozen five-coordinate Pareto relation and the canonical governance decision set. Repository, pinned-Mathlib, and third-party Lean searches found no existing stop certificate.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoFrontierStopDivergence.pareto_frontier_requires_sourced_orientation`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoWeakPreorder](ParetoWeakPreorder.md)
- Dependency: [D5/S3/ConceptDynamics/Governance/TargetLaunderingCriterion](../Governance/TargetLaunderingCriterion.md)
