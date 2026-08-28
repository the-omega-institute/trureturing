# Observation-Intervention-Counterfactual Kernel Chain

## Abstract

Counterfactual, interventional, and observational query kernels form a chain, and each inclusion can be strict.

**Lemma 1.1 (Interventional equality forces observational equality).**

$$\forall M \in DeterministicBoolSCM, N \in DeterministicBoolSCM,\; Int\left(M\right) = Int\left(N\right) \Rightarrow Obs\left(M\right) = Obs\left(N\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/ObservationInterventionCounterfactualChain.interventional_eq_implies_observational_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imported Boolean model has no treatment-assignment mechanism. Its observational law is therefore the outcome margin at the known factual treatment false.

This margin is one slice of the full interventional table. Equal interventional tables have equal false-treatment slices, so interventional indistinguishability implies observational indistinguishability.

**Theorem 1.2 (The observation kernel inclusion can be strict).**

$$\exists M \in DeterministicBoolSCM, N \in DeterministicBoolSCM,\; Obs\left(M\right) = Obs\left(N\right) \land Int\left(M\right) \ne Int\left(N\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/ObservationInterventionCounterfactualChain.observation_kernel_strictness_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One witness model always returns false, while the other copies the treatment. At factual treatment false their observed outcome counts agree.

At treatment true the first model still returns false and the second returns true. Their interventional tables differ, proving that the observational kernel can be strictly coarser.

**Theorem 1.3 (The three query kernels form a strictness-capable chain).**

$$\left(\forall M \in DeterministicBoolSCM, N \in DeterministicBoolSCM,\; CF\left(M\right) = CF\left(N\right) \Rightarrow Int\left(M\right) = Int\left(N\right)\right) \land \left(\left(\forall M \in DeterministicBoolSCM, N \in DeterministicBoolSCM,\; Int\left(M\right) = Int\left(N\right) \Rightarrow Obs\left(M\right) = Obs\left(N\right)\right) \land \left(\left(\exists M \in DeterministicBoolSCM, N \in DeterministicBoolSCM,\; Int\left(M\right) = Int\left(N\right) \land CF\left(M\right) \ne CF\left(N\right)\right) \land \left(\exists M \in DeterministicBoolSCM, N \in DeterministicBoolSCM,\; Obs\left(M\right) = Obs\left(N\right) \land Int\left(M\right) \ne Int\left(N\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/ObservationInterventionCounterfactualChain.observation_intervention_counterfactual_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The counterfactual-to-interventional inclusion and its strict witness are imported directly from the established Boolean SCM result. The observational inclusion follows by taking a table slice.

The imported strict witness separates counterfactual from interventional queries. The constant and treatment-copying models separately witness strictness between intervention and observation.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Causal/ObservationInterventionCounterfactualChain.interventional_eq_implies_observational_eq`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/ObservationInterventionCounterfactualChain.observation_intervention_counterfactual_chain`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/ObservationInterventionCounterfactualChain.observation_kernel_strictness_witness`
- Dependency: [D5/S3/ConceptDynamics/Interventions/CounterfactualKernelStrictlyFiner](../Interventions/CounterfactualKernelStrictlyFiner.md)
