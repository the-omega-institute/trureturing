# Ternary Treatment and Outcome Sharp Bounds

## Abstract

A three-level treatment, three-level outcome structural response model has closed-form sharp bounds with primal and dual witnesses.

The exogenous response type has four states. Its first bit records whether treatment zero produces outcome zero, and its second bit records whether treatment two produces outcome two.

Treatment one produces the neutral outcome one. The endpoint joint counterfactual query is therefore the true-true response cell, while the two endpoint interventional probabilities are its Boolean marginals.

A cap on endpoint disagreement is a linear cross-world dependence restriction. The generic finite coupling theorem supplies both the dual certificate and an exogenous law attaining every point of the interval.

**Theorem 1.1 (The ternary endpoint model inherits the coupling certificate).**

$$\forall mass \in ResponseType \to Real, zeroTargetMarginal \in Real, twoTargetMarginal \in Real, disagreementCap \in Real,\; \operatorname{IsEndpointModel}\left(mass, zeroTargetMarginal, twoTargetMarginal, disagreementCap\right) \Rightarrow \operatorname{EventCouplingDualCertificate}\left(mass, zeroTargetMarginal, twoTargetMarginal, disagreementCap\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/TernaryTreatmentOutcomeSharpBounds.endpoint_model_dual_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every endpoint model unfolds to a feasible two-event coupling plus the disagreement constraint. Its marginal rows therefore carry the same exact dual-slack certificate.

**Theorem 1.2 (The ternary endpoint joint query has an exact sharp interval).**

$$\forall zeroTargetMarginal \in Real, twoTargetMarginal \in Real, disagreementCap \in Real, target \in Real,\; \left(\operatorname{max}\left(\operatorname{max}\left(0, zeroTargetMarginal + twoTargetMarginal - 1\right), \frac{zeroTargetMarginal + twoTargetMarginal - disagreementCap}{2}\right) \le target \land target \le \operatorname{min}\left(zeroTargetMarginal, twoTargetMarginal\right)\right) \Leftrightarrow \left(\exists mass \in ResponseType \to Real,\; \operatorname{IsEndpointModel}\left(mass, zeroTargetMarginal, twoTargetMarginal, disagreementCap\right) \land \operatorname{endpointJointQuery}\left(mass\right) = target\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/TernaryTreatmentOutcomeSharpBounds.ternary_endpoint_joint_query_sharp_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed interval is necessary by certificate replay and sufficient by an explicit four-state exogenous response law. Both endpoints and every interior value are attained.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Causal/TernaryTreatmentOutcomeSharpBounds.endpoint_model_dual_certificate`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/TernaryTreatmentOutcomeSharpBounds.ternary_endpoint_joint_query_sharp_iff`
- Dependency: [D5/S3/ConceptDynamics/Causal/FiniteEventCouplingSharpBounds](FiniteEventCouplingSharpBounds.md)
