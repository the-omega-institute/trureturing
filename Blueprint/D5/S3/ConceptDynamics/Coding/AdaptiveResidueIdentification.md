# Adaptive Modular Identification

## Abstract

A four-state modular model is exactly identified by a two-step adaptive protocol, while every exact static suite uses three sensors.

**Theorem 1.1 (Adaptive identification is strictly cheaper than a fixed suite).**

$$\begin{aligned}X = \{0, 10, 15, 21\}, p \in \{2, 3, 5\}, \operatorname{q}\left(p, x\right) = \operatorname{decide}\left(\operatorname{mod}\left(x, p\right) = 1\right)\\\operatorname{fiber}\left(\operatorname{q}\left(2\right), false\right) = \{0, 10\}, \operatorname{fiber}\left(\operatorname{q}\left(2\right), true\right) = \{15, 21\}\\\exists pi: \operatorname{BinaryProtocol}\left(X, 2\right), \operatorname{UsesReadoutFamily}\left(q, pi\right) \land \operatorname{Injective}\left(\operatorname{transcript}\left(pi\right)\right)\\\operatorname{question}\left(pi, 0\right) = \operatorname{q}\left(2\right), \operatorname{question}\left(pi, 1, h\right) = \operatorname{if}\left(h_{0}, \operatorname{q}\left(5\right), \operatorname{q}\left(3\right)\right)\\\forall p \in \{2, 3, 5\}, \neg\operatorname{Injective}\left(q_{p}\right), \forall d < 2, \neg\operatorname{ExactAtDepth}\left(q, d\right)\\D_{ad}(X, q) = 2 \land D_{stat}(X, q) = 3 \land D_{ad}(X, q) < D_{stat}(X, q).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/AdaptiveResidueIdentification.two_step_adaptive_residue_identification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state carrier is exactly {0, 10, 15, 21}. The three Boolean readouts are constructed from reduction modulo 2, 3, and 5; on this carrier each observed remainder is zero or one.

The protocol first reads sensor 2. A zero leaves states 0 and 10, which sensor 3 separates. A one leaves states 15 and 21, which sensor 5 separates. Its two-bit transcript is injective.

Every protocol node is required to choose one of the supplied readouts. Cardinality rules out exact transcripts of depth zero or one, so the minimum adaptive depth is two.

Each individual sensor merges a state pair. More generally, omitting sensor 2 merges 0 with 15, omitting sensor 3 merges 0 with 10, and omitting sensor 5 merges 15 with 21. Thus an injective fixed suite needs all three sensors.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/AdaptiveResidueIdentification.two_step_adaptive_residue_identification`
- Dependency: [D5/S3/ConceptDynamics/Coding/FiberBinaryIdentification](FiberBinaryIdentification.md)
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
