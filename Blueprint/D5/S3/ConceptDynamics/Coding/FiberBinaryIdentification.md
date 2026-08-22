# Binary Identification within Concept Fibers

## Abstract

Arbitrary binary questions identify finite fiber targets at logarithmic depth.

**Theorem 1.1 (Arbitrary binary questions identify every finite fiber target).**

$$\begin{gathered}\forall X, C, Target,\\{}[\operatorname{Fintype}(X)] [\operatorname{Fintype}(C)] [\operatorname{Fintype}(Target)],\\{}q_{C}: X \to C, T: X \to Target,\\{}\exists pi: \operatorname{BinaryProtocol}(X, \operatorname{clog}(2, \operatorname{worstFiberDiversity}(q_{C}, T))),\\{}\operatorname{IdentifiesGiven}(q_{C}, T, pi).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FiberBinaryIdentification.arbitrary_binary_questions_identify_target` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite current concept readout and finite target, fiber target diversity counts the distinct target values realized at one coordinate. Worst fiber diversity is the finite maximum of those counts, with empty coordinate carriers contributing zero.

A binary protocol is indexed by its finite depth. At each round it selects a binary concept readout from the complete preceding bit history, and its transcript carries a consistency proof for all states and rounds.

The public existential returns such a protocol at exactly the ceiling binary-logarithm depth. Identification is direct: equal current coordinates and equal complete transcripts force equal targets.

The construction assigns an injective fixed-length bit vector to every target value realized in each fiber. The pinned natural logarithm bound supplies enough bit vectors, and the selected questions ask their bits in order.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FiberBinaryIdentification.arbitrary_binary_questions_identify_target`
