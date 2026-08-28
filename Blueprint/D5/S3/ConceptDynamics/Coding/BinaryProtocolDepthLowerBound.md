# Adaptive Binary Protocol Depth Lower Bound

## Abstract

Identifying a target by adaptive binary questions requires logarithmic fiber depth.

**Theorem 1.1 (Binary identification depth is bounded below by fiber diversity).**

$$\begin{gathered}\forall X, C, Target: \operatorname{Type},\\{}[\operatorname{Fintype}(X)], [\operatorname{Fintype}(C)],\\{}c: \operatorname{Concept}(X, C), t: \operatorname{Concept}(X, Target),\\{}d: \mathbb{N}, pi: \operatorname{BinaryProtocol}(X, d),\\{}identifies: \operatorname{IdentifiesGiven}(c, t, pi),\\{}\operatorname{clog}(2, \operatorname{worstFiberDiversity}(c, t)) \leq d.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BinaryProtocolDepthLowerBound.adaptive_binary_protocol_depth_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The current concept partitions the finite state carrier into fibers. Worst fiber diversity is the greatest number of distinct target values realized inside any one of those fibers.

A depth-d adaptive binary protocol records one bit per round. It identifies the target when equal current records and equal full transcripts force equal target values.

Reading every transcript bit as a fixed-width auxiliary label makes that label target-determining. The least-label theorem then forces d to be at least the ceiling logarithm to base two of worst fiber diversity.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/BinaryProtocolDepthLowerBound.adaptive_binary_protocol_depth_lower_bound`
- Dependency: [D5/S3/ConceptDynamics/Coding/BinaryRepairCost](BinaryRepairCost.md)
