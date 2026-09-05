# Labeled Prefix Occurrences

## Abstract

Finite labeled samples carry a canonical finite family of prefix occurrences with exact leaf and extension semantics.

**Theorem 1.1 (Finite-sample leaves recover the registered sparse inputs).**

$$\operatorname{prefixWord}(\operatorname{prefixSample}(P, N), \operatorname{leaf}(i)) = \operatorname{input}(P, i)$$

*Proof.* Machine-checked in Lean as `D5/S0/Automata/LabeledPrefixTree.prefixSample_leaf_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A prefix occurrence records a sample index and a legal cut position. The leaf occurrence is the full word, and the theorem identifies it exactly with the corresponding sparse-problem input.

Equal prefix words may have multiple occurrences. Their later identification is carried by proofs rather than silently quotienting the finite carrier.

## References

- Truth anchor: `D5/S0/Automata/LabeledPrefixTree.prefixSample_leaf_word`
- Dependency: [D5/S0/Automata/TypedPartialDFAOOverBase](TypedPartialDFAOOverBase.md)
