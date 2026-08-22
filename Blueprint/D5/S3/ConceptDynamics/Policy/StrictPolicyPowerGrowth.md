# Strict Policy Power Growth

## Abstract

Separating one coarse fiber with a finer readout strictly increases policy power.

**Theorem 1.1 (A separated coarse fiber yields a genuinely new policy).**

$$\forall X, C, D, U: \operatorname{Type}, q_{C}: X \to C, q_{D}: X \to D, x, y: X, {q_{C}(x) = q_{C}(y) \land q_{D}(x) \neq q_{D}(y) \land {\exists u_{0}, u_{1}: U, u_{0} \neq u_{1}}} \Rightarrow {\exists policy: X \to U, policy \in \operatorname{policyCapability}\left(q_{D}, U\right) \land \neg{policy \in \operatorname{policyCapability}\left(q_{C}, U\right)} \land policy(x) \neq policy(y)} \land {\forall coarsePolicy: X \to U, coarsePolicy \in \operatorname{policyCapability}\left(q_{C}, U\right) \Rightarrow coarsePolicy(x) = coarsePolicy(y)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Policy/StrictPolicyPowerGrowth.strict_policy_power_growth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let two states have the same coarse coordinate but distinct fine coordinates. Given two distinct actions, a decision rule on the fine coordinate can assign one action to the fine coordinate of the first state and the other action everywhere else. The induced state policy therefore distinguishes the two states.

Every policy available from the coarse readout factors through its coarse coordinate, so it must take equal values on those states. Consequently the separating policy belongs to the fine capability but not the coarse capability, while all coarse policies satisfy the universal non-separation conclusion.

The result needs neither surjectivity nor a global strict-refinement hypothesis: one explicitly separated pair inside a coarse fiber already witnesses strict local growth of policy power.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Policy/StrictPolicyPowerGrowth.strict_policy_power_growth`
