# Recursive Binary Tree Serialization

## Abstract

A recursive binary parser recovers each tagged FreeMagma tree and its unused suffix.

The two leaf atoms are encoded by false,false and false,true. A branch is marked by true and followed by the complete encodings of its two children. The parser consumes one complete tree code and returns the remaining suffix.

**Theorem 1.1 (Exact suffix-preserving recursive parsing).**

Lean statement: `D5/S0/Computability/Coding/BinaryTreeSerialization.serialization_spec`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Coding/BinaryTreeSerialization.serialization_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every tagged FreeMagma tree and every suffix, parsing the concatenated code and suffix reconstructs the tree and returns exactly that suffix. Injectivity, prefix freedom, and empty-suffix decoding are residual corollaries and are not separate claims here.

## References

- Truth anchor: `D5/S0/Computability/Coding/BinaryTreeSerialization.serialization_spec`
