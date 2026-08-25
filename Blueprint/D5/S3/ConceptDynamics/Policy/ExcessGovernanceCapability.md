# Excess Governance Capability

## Abstract

A higher readout can add policy capability although a lower readout already suffices for the target.

**Theorem 1.1 (Higher governance can add power without adding target necessity).**

$$\forall X, T, C, D, U: \operatorname{Type},\\{}target: X \to T, lower: X \to C, higher: X \to D,\\{}x, y: X,\\{}{\operatorname{Refines}\left(target, lower\right) \land \operatorname{Refines}\left(lower, higher\right) \land\\{}{lower(x) = lower(y) \land higher(x) \neq higher(y)} \land {\exists u0, u1: U, u0 \neq u1}} \Rightarrow\\{}{\operatorname{Refines}\left(target, higher\right) \land\\{}\operatorname{policyCapability}\left(lower, U\right) \subseteq \operatorname{policyCapability}\left(higher, U\right) \land\\{}{\exists p: X \to U, p \in \operatorname{policyCapability}\left(higher, U\right) \land \neg{p \in \operatorname{policyCapability}\left(lower, U\right)} \land p(x) \neq p(y)} \land\\{}{\forall p: X \to U, p \in \operatorname{policyCapability}\left(lower, U\right) \Rightarrow p(x) = p(y)}}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Policy/ExcessGovernanceCapability.excess_governance_capability_without_target_need` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The target, lower readout, higher readout, states, and actions are independent source primitives. The lower readout is publicly assumed already sufficient for the target, while the higher readout refines it.

A public pair of states records the extra distinction: the lower readout identifies the pair and the higher readout separates it. Two distinct actions make that distinction operational.

Refinement composition preserves target sufficiency at the higher readout. Policy monotonicity includes every lower policy in the higher capability, while strict policy growth constructs a higher-only policy that distinguishes the pair and proves all lower policies identify it.

All three proof components are exact repository hits and are applied directly; no sibling capability, refinement, or target object is redeclared.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Policy/ExcessGovernanceCapability.excess_governance_capability_without_target_need`
- Dependency: [D5/S3/ConceptDynamics/Policy/StrictPolicyPowerGrowth](StrictPolicyPowerGrowth.md)
- Dependency: [D5/S3/ConceptDynamics/Refinement/RefinementTransitivity](../Refinement/RefinementTransitivity.md)
