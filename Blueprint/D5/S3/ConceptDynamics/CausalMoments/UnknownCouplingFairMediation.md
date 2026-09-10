# UnknownCouplingFairMediation

## Abstract

Optimize both independent source laws exactly in the fair complete-mediation model with only mediator marginals supplied.

M is an arbitrary finite type with decidable equality. control and treated are normalized rational FiniteResponseLaw values on M. coupling is a law on M times M; law is a law on complete tables M to Bool. HasMediatorMarginals and FairCompleteOutcome are the existing original causal predicates. Independent mechanisms and the no-direct-effect equation are built into completeMediatorBenefit. target is rational; table and best are Boolean functions on the whole M carrier.

**Definition 1.1 (Combined selected mediator mass).**

$$\forall M, control, treated, table, (\operatorname{partitionWeight}(control, treated, table)) = ((\operatorname{linearObjective}(\lambda i, \operatorname{ite}(\operatorname{table}(i), 1, 0), \operatorname{mass}(control))) + (\operatorname{linearObjective}(\lambda i, \operatorname{ite}(\operatorname{table}(i), 1, 0), \operatorname{mass}(treated))))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/UnknownCouplingFairMediation.partitionWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the sum of control(i)+treated(i) over the selected original mediator states. Its full-carrier total is two.

**Definition 1.2 (Crossing score of one partition).**

$$\forall M, control, treated, table, (\operatorname{partitionScore}(control, treated, table)) = ((1) - (\lvert(\operatorname{partitionWeight}(control, treated, table)) - (1)\rvert))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/UnknownCouplingFairMediation.partitionScore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only the combined marginal weights enter this score. They do not specify an independent mediator coupling.

**Theorem 1.3 (Bound all compatible mediator couplings).**

$$\forall M, coupling, control, treated, table, (\operatorname{HasMediatorMarginals}(coupling, control, treated)) \Rightarrow ((\operatorname{mediatorCutMass}(coupling, table)) \le (\operatorname{partitionScore}(control, treated, table)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/UnknownCouplingFairMediation.mediatorCutMass_le_partitionScore` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pointwise crossing indicator is bounded both by the sum of endpoint labels and by its complement. All original marginal equalities are retained.

**Theorem 1.4 (Construct an attaining original mediator law).**

$$\forall M, control, treated, table, \exists coupling, (\operatorname{HasMediatorMarginals}(coupling, control, treated)) \land ((\operatorname{mediatorCutMass}(coupling, table)) = (\operatorname{partitionScore}(control, treated, table)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/UnknownCouplingFairMediation.exists_partition_attaining_coupling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing Boolean Frechet law supplies a maximal-crossing coarse plan. The exact lift returns every individual original marginal and the same cut expectation, including null partitions.

**Theorem 1.5 (Complete identified interval with both laws unknown).**

$$\forall M, control, treated, \exists best, (\forall table, (\operatorname{partitionScore}(control, treated, table)) \le (\operatorname{partitionScore}(control, treated, best))) \land (\forall target, (\exists coupling, law, (\operatorname{HasMediatorMarginals}(coupling, control, treated)) \land (\operatorname{FairCompleteOutcome}(law)) \land ((\operatorname{completeMediatorBenefit}(coupling, law)) = (target))) \Leftrightarrow (((0) \le (target)) \land ((target) \le (\frac{\operatorname{partitionScore}(control, treated, best)}{2}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/UnknownCouplingFairMediation.unknown_coupling_fair_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The optimal partition is obtained over the full finite carrier. One constructed mediator coupling already attains all intermediate targets through the existing fixed-coupling outcome-mixture theorem. No optimal coupling is assumed.

**Theorem 1.6 (Exact one-half saturation criterion).**

$$\forall M, control, treated, (\exists coupling, law, (\operatorname{HasMediatorMarginals}(coupling, control, treated)) \land (\operatorname{FairCompleteOutcome}(law)) \land ((\operatorname{completeMediatorBenefit}(coupling, law)) = (\frac{1}{2}))) \Leftrightarrow (\exists table, (\operatorname{partitionWeight}(control, treated, table)) = (1))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/UnknownCouplingFairMediation.unknown_coupling_half_iff_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is an exact subset-partition condition on the combined mediator marginals. It is not a claim that generic nonfair or additionally restricted models have the same optimum.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/UnknownCouplingFairMediation.exists_partition_attaining_coupling`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/UnknownCouplingFairMediation.mediatorCutMass_le_partitionScore`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/UnknownCouplingFairMediation.partitionScore`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/UnknownCouplingFairMediation.partitionWeight`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/UnknownCouplingFairMediation.unknown_coupling_fair_interval`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/UnknownCouplingFairMediation.unknown_coupling_half_iff_partition`
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds](CompleteMediatorCutSharpBounds.md)
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/FiniteCouplingPushforwardLift](FiniteCouplingPushforwardLift.md)
