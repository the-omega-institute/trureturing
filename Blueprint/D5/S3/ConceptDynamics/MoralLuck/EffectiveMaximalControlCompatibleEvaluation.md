# Effective Maximal Control-Compatible Evaluation

## Abstract

The canonical common coarsening is the maximal control-compatible evaluation.

**Theorem 1.1 (The common coarsening is maximal among control-compatible evaluations).**

$$\begin{gathered}\forall X: \operatorname{Type},\\{}E_J, C_{ctl}, K \in \operatorname{EffectiveConcept}(X),\\{}\operatorname{commonCoarsening}(\operatorname{readout}(E_J), \operatorname{readout}(C_{ctl})) \leq \operatorname{readout}(E_J) \land\\{}\operatorname{commonCoarsening}(\operatorname{readout}(E_J), \operatorname{readout}(C_{ctl})) \leq \operatorname{readout}(C_{ctl}) \land\\{}((\operatorname{readout}(K) \leq \operatorname{readout}(E_J) \land \operatorname{readout}(K) \leq \operatorname{readout}(C_{ctl})) \Rightarrow \operatorname{readout}(K) \leq \operatorname{commonCoarsening}(\operatorname{readout}(E_J), \operatorname{readout}(C_{ctl}))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/MoralLuck/EffectiveMaximalControlCompatibleEvaluation.maximal_control_compatible_evaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluation, control, and candidate are effective concepts: each readout is surjective onto its coordinate carrier. This is the effective quotient context of the common-coarsening construction and does not require the source carrier to be inhabited.

The public fair evaluation is the imported canonical quotient by the supremum of the evaluation and control kernel relations. The first two conjuncts state its factorization through each input readout.

The final public conjunct keeps the two candidate assumptions grouped. Reverse kernel inclusion turns them into the two bounds whose supremum proves the maximal factorization.

The proof directly applies the concept-family reverse-kernel criterion, the canonical common-coarsening primitive, and the pinned setoid complete-lattice laws.

## References

- Truth anchor: `D5/S3/ConceptDynamics/MoralLuck/EffectiveMaximalControlCompatibleEvaluation.maximal_control_compatible_evaluation`
- Dependency: [D5/S3/ConceptDynamics/Refinement/ConceptKernelOrderDuality](../Refinement/ConceptKernelOrderDuality.md)
