# Observation-Intervention-Counterfactual Query-Kernel Hierarchy

## Abstract

Nested observational, interventional, and counterfactual query families induce a kernel chain, and both links admit concrete strictness witnesses.

**Theorem 1.1 (Nested query families induce the kernel hierarchy).**

$$\forall M \in \operatorname{Type}, ObsIndex \in \operatorname{Type}, IntIndex \in \operatorname{Type}, CfIndex \in \operatorname{Type}, ObsAnswer \in ObsIndex \to \operatorname{Type}, IntAnswer \in IntIndex \to \operatorname{Type}, CfAnswer \in CfIndex \to \operatorname{Type}, obsQuery \in (oi: ObsIndex) \to M \to ObsAnswer(oi), intQuery \in (ii: IntIndex) \to M \to IntAnswer(ii), cfQuery \in (ci: CfIndex) \to M \to CfAnswer(ci), obsToInt \in ObsIndex \to IntIndex, intToCf \in IntIndex \to CfIndex, obsFromInt \in (oi: ObsIndex) \to IntAnswer(obsToInt(oi)) \to ObsAnswer(oi), intFromCf \in (ii: IntIndex) \to CfAnswer(intToCf(ii)) \to IntAnswer(ii), hObs \in \left(\forall oi \in ObsIndex, m \in M,\; obsFromInt(oi, intQuery(obsToInt(oi), m)) = obsQuery(oi, m)\right), hInt \in \left(\forall ii \in IntIndex, m \in M,\; intFromCf(ii, cfQuery(intToCf(ii), m)) = intQuery(ii, m)\right),\; \left(\forall m \in M, n \in M,\; queryKernel(cfQuery, m, n) \Rightarrow queryKernel(intQuery, m, n)\right) \land \left(\left(\forall m \in M, n \in M,\; queryKernel(intQuery, m, n) \Rightarrow queryKernel(obsQuery, m, n)\right) \land \left(\left(\exists S \in DeterministicBoolSCM, T \in DeterministicBoolSCM,\; Int(S) = Int(T) \land CF(S) \ne CF(T)\right) \land \left(\exists S \in DeterministicBoolSCM, T \in DeterministicBoolSCM,\; Obs(S) = Obs(T) \land Int(S) \ne Int(T)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/QueryKernelHierarchy.query_kernel_hierarchy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each observational answer is read from a designated interventional answer, and each interventional answer is read from a designated counterfactual answer. Equality at the richer layer therefore forces equality at the next layer.

The two final clauses reuse the established Boolean structural-model countermodels. One separates equal single-world intervention answers from cross-world responses; the other separates equal observations from intervention answers.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Causal/QueryKernelHierarchy.query_kernel_hierarchy`
- Dependency: [D5/S3/ConceptDynamics/Causal/ObservationInterventionCounterfactualChain](ObservationInterventionCounterfactualChain.md)
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/QueryFamilyIdentification](../Sufficiency/QueryFamilyIdentification.md)
