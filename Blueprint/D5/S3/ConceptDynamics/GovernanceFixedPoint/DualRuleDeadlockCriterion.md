# Dual-Rule Deadlock Criterion

## Abstract

A repair class is deadlocked exactly when it has no jointly allowed repair.

**Theorem 1.1 (Deadlock is empty joint allowance).**

$$\begin{aligned}\forall Repair: \operatorname{Type},\\\forall repairClass, allow_{1}, allow_{2}: Set(Repair),\\{}\\Deadlocked(repairClass, allow_{1}, allow_{2}) \Leftrightarrow \\\operatorname{intersection}\left(repairClass, JointAllowed(allow_{1}, allow_{2})\right) = \emptyset.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GovernanceFixedPoint/DualRuleDeadlockCriterion.deadlocked_iff_empty_joint_allowance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen reachability predicate asks for a repair in both the repair class and the two rules' joint allowance. Negating that witness is equivalent to emptiness of the same intersection.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/DualRuleDeadlockCriterion.deadlocked_iff_empty_joint_allowance`
- Dependency: [D5/S3/ConceptDynamics/GovernanceFixedPoint/Core](Core.md)
