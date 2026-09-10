# Binary Zeckendorf First-Return Skeleton

## Abstract

Binary Zeckendorf words admit a first-return block code, and transient typed-DFAO states collapse to output-and-return signatures without increasing state count.

**Theorem 1.1 (Canonical signature reconstruction preserves behaviour and does not add states).**

Lean statement: `D5/S0/Automata/BinaryZeckendorfBlockSkeleton.canonical_extract_behavior_and_cardinality`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/BinaryZeckendorfBlockSkeleton.canonical_extract_behavior_and_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recurrent fiber is retained verbatim, while one canonical transient state is introduced for each distinct output-and-zero-successor signature used by a recurrent one transition.

The reconstructed typed partial DFAO agrees with the original machine on every legal block code. An explicit injection from canonical states into original states proves that canonicalization never increases finite cardinality.

## References

- Truth anchor: `D5/S0/Automata/BinaryZeckendorfBlockSkeleton.canonical_extract_behavior_and_cardinality`
- Dependency: [D5/S0/Automata/BinaryZeckendorfBlockSkeletonCore](BinaryZeckendorfBlockSkeletonCore.md)
- Dependency: [D5/S0/Automata/TypedPartialDFAOOverBase](TypedPartialDFAOOverBase.md)
