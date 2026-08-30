# Conservative Channel Addition

## Abstract

Every deadlocked repair class can be added as an exact conservative channel.

**Theorem 1.1 (A conservative channel exists for every deadlocked repair class).**

$$\begin{aligned}\forall Repair: \operatorname{Type},\\\forall repairClass, allow_{1}, allow_{2}: Set(Repair),\\{}\\Deadlocked(repairClass, allow_{1}, allow_{2}) \Rightarrow \\\exists channel: Set(Repair),\\{}\\ConservativeChannel(repairClass, allow_{1}, allow_{2}, channel).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GovernanceFixedPoint/ConservativeChannelAddition.conservative_channel_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit channel is the repair class itself. Deadlock makes that class disjoint from the old joint allowance, so adjoining the channel preserves every old allowance and adds exactly the repair class.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/ConservativeChannelAddition.conservative_channel_exists`
- Dependency: [D5/S3/ConceptDynamics/GovernanceFixedPoint/DualRuleDeadlockCriterion](DualRuleDeadlockCriterion.md)
