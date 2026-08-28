# Binary Identification and Repair Depth Equality

## Abstract

Unconstrained binary identification has the same least depth as exact repair width.

**Theorem 1.1 (Least adaptive depth equals least binary repair width).**

$$\begin{gathered}\forall X, C, Target: \operatorname{Type},\\{}[\operatorname{Fintype}(X)], [\operatorname{Fintype}(C)],\\{}c: X \to C, t: X \to Target,\\{}\exists dAdaptive, dRepair \in \mathbb{N},\\{}\operatorname{IsLeast}(\{d \in \mathbb{N} \mid \exists pi: \operatorname{BinaryProtocol}(X, d), \operatorname{IdentifiesGiven}(c, t, pi)\}, dAdaptive) \land\\{}\operatorname{IsLeast}(\{k \in \mathbb{N} \mid \operatorname{BinaryRepairFeasible}(c, t, k)\}, dRepair) \land\\{}dAdaptive = dRepair \land\\{}dRepair = \operatorname{clog}(2, \operatorname{worstFiberDiversity}(c, t)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Identifiability/BinaryIdentificationRepairDepthEquality.unconstrained_binary_identification_depth_equals_repair_bits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Worst fiber diversity counts the largest number of target values realized under one current-concept coordinate.

The public statement exposes both least-element claims. The adaptive membership clause contains an identifying protocol, while the repair membership clause contains a target-determining bit label.

The frozen construction, adaptive lower bound, and exact repair-cost theorem give the common ceiling binary logarithm.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Identifiability/BinaryIdentificationRepairDepthEquality.unconstrained_binary_identification_depth_equals_repair_bits`
- Dependency: [D5/S3/ConceptDynamics/Coding/BinaryProtocolDepthLowerBound](../Coding/BinaryProtocolDepthLowerBound.md)
