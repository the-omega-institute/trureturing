# Successor sets in compatible single cycles

## Abstract

A contracted cycle count bounds the probability of a set of possible successors.

**Theorem 1.1 (Probability bound for a set of compatible successors).**

Lean statement: `D5/S3/Combinatorics/Graph/LinearForests/AlternatingSuccessorSetBound.successor_set_mass_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LinearForests/AlternatingSuccessorSetBound.successor_set_mass_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Give each label a source and a destination color, each taking one of two values. Sample uniformly among single cycles on the finite label set in which each label's destination color equals its successor's source color. Assume both source colors occur at least twice. For a specified label and a target set excluding that label, the probability that its successor belongs to the target set is at most the target set's size divided by one less than the number of labels whose source color matches the specified destination color.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LinearForests/AlternatingSuccessorSetBound.successor_set_mass_le`
- Dependency: [D5/S3/Combinatorics/Graph/LinearForests/AlternatingConnectorLaw](AlternatingConnectorLaw.md)
