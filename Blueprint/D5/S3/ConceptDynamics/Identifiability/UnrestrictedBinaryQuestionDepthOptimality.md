# Unrestricted Binary Question Depth

## Abstract

Unrestricted binary questions attain the exact finite repair depth.

**Theorem 1.1 (Adaptive identification and exact repair have the same least width).**

$$\begin{aligned}\forall X, C, Target,\\\operatorname{Fintype}(X) \land \operatorname{Fintype}(C),\\c: X \to C, t: X \to Target,\\\operatorname{IsLeast}(\{d \in \mathbb{N} \mid \exists pi: \operatorname{BinaryProtocol}(X, d), \operatorname{IdentifiesGiven}(c, t, pi)\}, \operatorname{clog}(2, \operatorname{worstFiberDiversity}(c, t))) \land\\\operatorname{IsLeast}(\{k \in \mathbb{N} \mid \operatorname{BinaryRepairFeasible}(c, t, k)\}, \operatorname{clog}(2, \operatorname{worstFiberDiversity}(c, t))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Identifiability/UnrestrictedBinaryQuestionDepthOptimality.unrestricted_binary_question_depth_optimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical protocol assigns fixed-length bit vectors to target values realized within each current-concept fiber and asks their bits sequentially.

The protocol construction attains the ceiling binary logarithm of worst fiber diversity. The adaptive lower bound and the exact binary-label minimum show that the same width is least for both tasks.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Identifiability/UnrestrictedBinaryQuestionDepthOptimality.unrestricted_binary_question_depth_optimality`
- Dependency: [D5/S3/ConceptDynamics/Coding/BinaryProtocolDepthLowerBound](../Coding/BinaryProtocolDepthLowerBound.md)
