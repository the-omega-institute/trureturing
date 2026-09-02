# Two-Bit Joint and Common Knowledge Separation

## Abstract

Two coordinate observers have complete pooled knowledge but only constant common knowledge.

**Theorem 1.1 (Pooled knowledge is complete while common knowledge is trivial).**

$$\begin{gathered}X := Bool \times Bool,\\{}q_{1} = pi_{1}, q_{2} = pi_{2},\\{}K_{pool} = ker\left(conceptJoin\left(q_{1}, q_{2}\right)\right) = Delta_{X},\\{}Obs\left(K_{pool}\right) = Fun\left(X, Bool\right),\\{}K_{common} = ker\left(commonCoarsening\left(q_{1}, q_{2}\right)\right) = X \times X,\\{}Obs\left(K_{common}\right) = Const\left(X, Bool\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/TwoBitJointCommonKnowledgeSeparation.two_bit_joint_common_knowledge_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state space is the Boolean square. The first observer reads only the first coordinate and the second observer reads only the second.

The joint readout kernel is equality, so every Boolean-valued state function is pooled-observable.

Alternating the two individual kernel relations connects every pair of states. The common coarsening is therefore universal, and its Boolean-valued observable functions are exactly the constants.

## References

- Truth anchor: `D5/S3/ConceptDynamics/TwoBitJointCommonKnowledgeSeparation.two_bit_joint_common_knowledge_separation`
- Dependency: [D5/S3/ConceptDynamics/Refinement/ConceptKernelOrderDuality](Refinement/ConceptKernelOrderDuality.md)
