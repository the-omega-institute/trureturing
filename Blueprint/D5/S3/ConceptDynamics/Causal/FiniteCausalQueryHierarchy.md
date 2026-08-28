# Finite Causal Query Hierarchy

## Abstract

One finite Boolean SCM class carries genuine observational, interventional, and counterfactual query profiles with both hierarchy links strict.

**Theorem 1.1 (The finite causal query hierarchy is strict).**

$$\left(\forall M \in FiniteBoolSCM,\; \forall N \in FiniteBoolSCM,\; CF\left(M\right) = CF\left(N\right) \Rightarrow Int\left(M\right) = Int\left(N\right)\right) \land \left(\left(\forall M \in FiniteBoolSCM,\; \forall N \in FiniteBoolSCM,\; Int\left(M\right) = Int\left(N\right) \Rightarrow Obs\left(M\right) = Obs\left(N\right)\right) \land \left(\left(Obs\left(observationalForwardModel\right) = Obs\left(observationalReverseModel\right) \land Int\left(observationalForwardModel\right) \ne Int\left(observationalReverseModel\right)\right) \land \left(Int\left(stableCouplingModel\right) = Int\left(flipCouplingModel\right) \land CF\left(stableCouplingModel\right) \ne CF\left(flipCouplingModel\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/FiniteCausalQueryHierarchy.finite_causal_query_hierarchy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The common carrier is a two-node recursive Boolean structural model. Its exogenous state has two coordinates, so the same class includes both reverse causal direction and independent outcome noise.

The interventional profile contains the empty intervention. Its empty component is the passive joint law, while the counterfactual profile retains the response of each exogenous state under every regime.

The forward and reverse direction models have the same passive law but different intervention laws. The stable and flip coupling models have the same complete single-world profile but different unit-preserving response profiles.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Causal/FiniteCausalQueryHierarchy.finite_causal_query_hierarchy`
- Dependency: [D5/S3/ConceptDynamics/Interventions/ObservationInterventionSeparation](../Interventions/ObservationInterventionSeparation.md)
