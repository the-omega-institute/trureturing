# Counterfactual Kernel Is Strictly Finer

## Abstract

Counterfactual equality determines interventional equality for deterministic Boolean models, but interventional equality does not determine the counterfactual table.

**Lemma 1.1 (The interventional table is the counterfactual collapse).**

$$\forall M \in DeterministicBoolSCM,\; \operatorname{Int}\left(M\right) = \operatorname{collapse}\left(\operatorname{CF}\left(M\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interventions/CounterfactualKernelStrictlyFiner.intervention_eq_collapse_counterfactual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The counterfactual table retains the exogenous unit, the factual treatment, and the alternate treatment. Collapsing it sums over the two exogenous units for each imposed treatment and outcome.

For tables produced by a deterministic Boolean causal model, the factual-treatment coordinate does not affect this aggregate. The resulting counts are exactly the model's interventional table, so the interventional readout factors through the counterfactual readout.

**Lemma 1.2 (Counterfactual equality forces interventional equality).**

$$\forall M \in DeterministicBoolSCM, N \in DeterministicBoolSCM,\; \operatorname{CF}\left(M\right) = \operatorname{CF}\left(N\right) \Rightarrow \operatorname{Int}\left(M\right) = \operatorname{Int}\left(N\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interventions/CounterfactualKernelStrictlyFiner.counterfactual_eq_implies_interventional_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two deterministic Boolean causal models with the same counterfactual table have the same image under the collapse map. Since that image is each model's interventional table, their interventional readouts must agree.

Thus counterfactual indistinguishability is stronger than interventional indistinguishability: every equality in the counterfactual kernel descends to one in the interventional kernel.

**Theorem 1.3 (The counterfactual kernel is strictly finer).**

$$\left(\forall M \in DeterministicBoolSCM, N \in DeterministicBoolSCM,\; \operatorname{CF}\left(M\right) = \operatorname{CF}\left(N\right) \Rightarrow \operatorname{Int}\left(M\right) = \operatorname{Int}\left(N\right)\right) \land \left(\exists M \in DeterministicBoolSCM, N \in DeterministicBoolSCM,\; \operatorname{Int}\left(M\right) = \operatorname{Int}\left(N\right) \land \operatorname{CF}\left(M\right) \ne \operatorname{CF}\left(N\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interventions/CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Counterfactual equality always implies interventional equality by the collapse factorization. This establishes inclusion of the counterfactual kernel in the interventional kernel.

The strictness witness consists of two deterministic Boolean models whose outcome counts agree under every intervention while their unit-level counterfactual tables differ. Hence the converse kernel inclusion fails.

The source-family registrations retain Int and CF on the original DeterministicBoolSCM carrier, with their original table output types. Their complete laws include the existential separation and, for strictness, universal kernel inclusion. The audit checks source correspondence and sensitivity with other roles fixed: constant CF destroys separation, while injective outcome-table encoding in the Int slot removes collisions.

The Int readout is both allSingleWorldMarginals and interventionMarginal, and CF is counterfactualJoint. The no-effect and flip-effect models occupy one marginal fiber but disagree on that target. The existing identifiability and sufficiency results therefore refute a decoder from Int to CF. Forward refinement uses the global collapse proof; the separating pair alone does not establish refinement.

These conclusions concern deterministic Boolean models and counts over the uniform two-unit exogenous population. The source-family residual remains explicitly open; this does not negate the proved target-specific loss or claim that arbitrary proof dependencies ensure fidelity or eventual discovery of every defect.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Interventions/CounterfactualKernelStrictlyFiner.counterfactual_eq_implies_interventional_eq`
- Truth anchor: `D5/S3/ConceptDynamics/Interventions/CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer`
- Truth anchor: `D5/S3/ConceptDynamics/Interventions/CounterfactualKernelStrictlyFiner.intervention_eq_collapse_counterfactual`
- Dependency: [D5/S3/ConceptDynamics/Interventions/InterventionCounterfactualSeparation](InterventionCounterfactualSeparation.md)
