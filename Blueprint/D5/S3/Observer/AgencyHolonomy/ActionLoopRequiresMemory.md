# Action Loop Requires Memory

## Abstract

A policy-visible loop effect requires nontrivial memory transport.

**Theorem 1.1 (Policy change implies memory change).**

$$\forall x3 \in \left(\forall x3 \in \mathord{\cdot},\; \forall x4 \in \mathord{\cdot},\; \mathord{\cdot}\right),\; \forall x4 \in \mathord{\cdot},\; \forall x5 \in \left(\forall x5 \in \mathord{\cdot},\; \mathord{\cdot}\right),\; \forall x6 \in \mathord{\cdot},\; \mathit{x3}\left(\mathit{x4}, \mathit{x5}\left(\mathit{x6}\right)\right) \ne \mathit{x3}\left(\mathit{x4}, \mathit{x6}\right) \Rightarrow \mathit{x5}\left(\mathit{x6}\right) \ne \mathit{x6}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/ActionLoopRequiresMemory.policy_change_implies_memory_change` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a question, memory state, memory transport, and policy. Assume the transport changes the policy's selected action.

If the transported memory were unchanged, the two policy evaluations would coincide. The visible action change therefore forces a memory change.

**Theorem 1.2 (An injective policy coordinate detects memory change).**

$$\forall policy: Q \to \left(M \to A\right), q: Q, h: M \to M, m: M,\\{}(\operatorname{Injective}\left(\operatorname{policy}\left(q\right)\right) \land \operatorname{h}\left(m\right) \neq m) \Rightarrow \operatorname{policy}\left(q, \operatorname{h}\left(m\right)\right) \neq \operatorname{policy}\left(q, m\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/ActionLoopRequiresMemory.injective_policy_detects_memory_change` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the converse direction, assume the policy at the chosen question is injective as a function of memory.

A nontrivial memory transport must then change the selected action at that memory state. No injectivity is assumed at other questions.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/ActionLoopRequiresMemory.injective_policy_detects_memory_change`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/ActionLoopRequiresMemory.policy_change_implies_memory_change`
