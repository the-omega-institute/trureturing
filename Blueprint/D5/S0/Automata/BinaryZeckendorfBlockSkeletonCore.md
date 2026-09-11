# Binary Zeckendorf Block Codes and Transient Signatures

## Abstract

Binary Zeckendorf return-block codes are uniquely decodable, and transient typed-DFAO signatures determine every continuation.

**Theorem 1.1 (The return-block code is uniquely decodable).**

Lean statement: `D5/S0/Automata/BinaryZeckendorfBlockSkeletonCore.compressLegalWord_expand`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/BinaryZeckendorfBlockSkeletonCore.compressLegalWord_expand` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every legal binary Zeckendorf word factors into the first-return blocks 0 and 10, followed by either no terminal symbol or one final 1. Expansion followed by legal-word compression recovers the original code.

**Theorem 1.2 (A transient signature determines every continuation).**

Lean statement: `D5/S0/Automata/BinaryZeckendorfBlockSkeletonCore.same_oneSignature_evalFromState`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/BinaryZeckendorfBlockSkeletonCore.same_oneSignature_evalFromState` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A state over the previous-one base state has no legal one transition. Its current output and optional zero-successor therefore determine its evaluation on every continuation, including undefined continuations.

## References

- Truth anchor: `D5/S0/Automata/BinaryZeckendorfBlockSkeletonCore.compressLegalWord_expand`
- Truth anchor: `D5/S0/Automata/BinaryZeckendorfBlockSkeletonCore.same_oneSignature_evalFromState`
- Dependency: [D5/S0/Automata/TypedPartialDFAOOverBase](TypedPartialDFAOOverBase.md)
