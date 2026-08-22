# Policy Capability Monotonicity

## Abstract

Refining a readout enlarges its implementable policy set.

**Theorem 1.1 (Policy capability is monotone under refinement).**

$$\forall X, C, D, U: \operatorname{Type}, q_{C}: X \to C, q_{D}: X \to D,\ \operatorname{Refines}\left(q_{C}, q_{D}\right) \Rightarrow \operatorname{policyCapability}\left(q_{C}, U\right) \subseteq \operatorname{policyCapability}\left(q_{D}, U\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PolicyCapabilityMonotonicity.policy_capability_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The policy-capability set of a readout consists of all state-level actions obtained by composing the readout with a decision rule.

A refinement factor recovers the coarse value from the fine value. Precomposing every coarse decision rule with that factor gives the stated inclusion of policy-capability sets.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PolicyCapabilityMonotonicity.policy_capability_monotone`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](ConceptJoinUniversal.md)
