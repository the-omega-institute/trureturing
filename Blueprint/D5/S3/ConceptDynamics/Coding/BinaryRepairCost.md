# Binary Repair Cost

## Abstract

Binary repair costs exactly the ceiling binary logarithm of fiber diversity.

**Theorem 1.1 (Binary repair width is the logarithm of minimal labels).**

$$\begin{gathered}\forall X, C, Target,\\{}[\operatorname{Fintype}(X)] [\operatorname{Fintype}(C)],\\{}r: X \to C, t: X \to Target,\\{}d = \operatorname{worstFiberDiversity}(r, t),\\{}(\forall k \in \mathbb{N}, \operatorname{BinaryRepairFeasible}(r, t, k) \iff d \leq 2^{k}) \land\\{}\operatorname{IsLeast}(\{k \in \mathbb{N} \mid \operatorname{BinaryRepairFeasible}(r, t, k)\}, \operatorname{clog}(2, d)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BinaryRepairCost.binary_repair_cost_is_log_of_minimal_labels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A width-k binary repair label assigns one k-bit string to each state. It determines the target relative to the original record when states with the same record and the same string must have the same target outcome.

There are exactly 2^k fixed-width bit strings. Consequently, width k is feasible precisely when this code space is at least as large as the greatest number of distinct target outcomes occurring in one record fiber.

The forward direction converts any binary label into a finite label and invokes the minimum-label lower bound. For the reverse direction, a minimum exact label is embedded into the available bit strings, preserving target determination inside every fiber.

It follows that the least feasible width is the ceiling logarithm to base two of worst fiber diversity, including the zero-diversity case governed by the natural-number ceiling logarithm.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/BinaryRepairCost.binary_repair_cost_is_log_of_minimal_labels`
- Dependency: [D5/S3/ConceptDynamics/Appeal/MinimalAppealLabelCount](../Appeal/MinimalAppealLabelCount.md)
