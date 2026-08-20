# Controlled Relation Recursion

## Abstract

Bounded controlled behavior relations satisfy the current-readout recursion.

**Theorem 1.1 (Controlled behavior relations obey the one-step recursion).**

$$\forall Y, U, O,\ F: U \to Y \to Y, q: Y \to O, m\in \mathbb{N},\ \operatorname{R}(F, q, 0) = \operatorname{ker}(q) \land\ \operatorname{R}(F, q, m+1) = \operatorname{inter}(\operatorname{ker}(q), \operatorname{iInter}(u \in U, \operatorname{preimage}(\operatorname{pairMap}(\operatorname{F}(u), \operatorname{F}(u)), \operatorname{R}(F, q, m)))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/ControlledRelationRecursion.controlled_behavior_relation_recursion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary state, input, and readout carriers, construct the depth-m relation by requiring equal readouts after every input word of length at most m. The current-readout kernel is separately constructed from equality under the readout map.

At depth zero only the empty input word is tested, giving the readout kernel. At depth m+1, splitting a word into the empty word or an initial input followed by a word of length at most m gives the kernel intersected with every successor-pair preimage.

Repository search found and reuses runWord and boundedWordEquivalent from the frozen controlled behavior modules. Pinned Mathlib search found Set.ext, Set.mem_iInter, and Set.mem_preimage. No packaged theorem containing both recursion clauses was found.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ControlledRelationRecursion.controlled_behavior_relation_recursion`
- Dependency: [D5/S3/ObserverMemory/Algorithms/ControlledSignatureStabilization](ControlledSignatureStabilization.md)
