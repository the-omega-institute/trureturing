# Three-Layer Causal Observation Language

## Abstract

Observational, interventional, and counterfactual profiles induce a strict kernel hierarchy under exactly the two stated family-membership premises.

**Definition 1.1 (Observational profile).**

Lean statement: `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.observationalProfile`

*Formalization.* `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.observationalProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The passive profile is the joint visible-variable law with no mechanism replacement.

**Definition 1.2 (Interventional profile).**

Lean statement: `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.interventionalProfile`

*Formalization.* `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.interventionalProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The interventional profile restricts the single-world law family to the declared set of allowed interventions.

**Definition 1.3 (Counterfactual profile).**

Lean statement: `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.counterfactualProfile`

*Formalization.* `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.counterfactualProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The counterfactual profile restricts query laws to the declared query set.

**Definition 1.4 (Three-layer equivalence).**

Lean statement: `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.threeLayerEquivalence`

*Formalization.* `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.threeLayerEquivalence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three equivalence relations are the Setoid kernels of the three profile maps.

**Theorem 1.5 (The causal profile kernels form the stated chain).**

$$\left(emptyAllowed \land singleWorldQueried\right) \Rightarrow \left(ker\left(cfQ\right) \le ker\left(intA\right) \land ker\left(intA\right) \le ker\left(Obs\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.causal_hierarchy_direction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty-intervention law recovers observation, while each selected single-world counterfactual law recovers its intervention law.

**Theorem 1.6 (The intervention kernel is not below the counterfactual kernel).**

$$\neg ker\left(Int\right) \le ker\left(CF\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.intervention_kernel_not_below_counterfactual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stable and flip Boolean SCMs agree on every single-world regime law but disagree on the unit-preserving counterfactual response.

**Theorem 1.7 (The observation kernel is not below the intervention kernel).**

$$\neg ker\left(Obs\right) \le ker\left(Int\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.observation_kernel_not_below_intervention` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward and reverse Boolean SCMs have one passive joint law but are separated by a perfect intervention on X.

**Theorem 1.8 (The empty-intervention premise is necessary).**

$$\left(\neg empty \in A\right) \land \left(\neg ker\left(intA\right) \le ker\left(Obs\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.empty_intervention_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A concrete Boolean profile omits its null action. The selected intervention profile is constant although observation still separates the models.

**Theorem 1.9 (The single-world-query premise is necessary).**

$$Q = emptySet \land \left(\neg ker\left(cfQ\right) \le ker\left(intA\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.single_world_query_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An empty counterfactual query family has a universal kernel while the sole intervention query retains the Boolean model value.

**Theorem 1.10 (Singleton query families collapse the hierarchy).**

$$ker\left(cfQ\right) = ker\left(intA\right) \land ker\left(intA\right) = ker\left(Obs\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.singleton_query_families_collapse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the only intervention is empty and the only counterfactual query is its single-world result, the two law bridges identify all three kernels.

**Theorem 1.11 (A one-point law space collapses the hierarchy).**

$$ker\left(cfUnit\right) = ker\left(intUnit\right) \land ker\left(intUnit\right) = ker\left(obsUnit\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.unit_law_space_collapses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every profile into Unit is constant, independently of the model, action, or query carriers.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.causal_hierarchy_direction`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.counterfactualProfile`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.empty_intervention_is_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.intervention_kernel_not_below_counterfactual`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.interventionalProfile`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.observation_kernel_not_below_intervention`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.observationalProfile`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.single_world_query_is_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.singleton_query_families_collapse`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.threeLayerEquivalence`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.unit_law_space_collapses`
- Dependency: [D5/S3/ConceptDynamics/Causal/FiniteCausalQueryHierarchy](FiniteCausalQueryHierarchy.md)
