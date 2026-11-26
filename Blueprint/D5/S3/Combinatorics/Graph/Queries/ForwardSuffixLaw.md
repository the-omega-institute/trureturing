# The likelihood of fresh binary slots

## Abstract

Conditioning on observed binary slots leaves distinct unused positions uniform.

**Theorem 1.1 (One factor of one half for each newly observed position).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/ForwardSuffixLaw.suffix_after_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/ForwardSuffixLaw.suffix_after_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a finite set of positions with two distinct available values at each position. Draw independently uniform orders of their two slots. Fix an earlier observation and a later observation, each specifying values at any subset of slots. The positions with at least one specified slot in the two observations are disjoint.

Assume the earlier observation is compatible with the available values and the two-slot distinctness condition. Given that observation, a compatible later observation has probability two to the minus number of its observed positions. An incompatible later observation has probability zero.

A table matches both observations exactly when it matches their union. Compatibility of the union is equivalent to the two separate compatibility conditions. The visited positions of the union are a disjoint union, so the power of two for the earlier positions cancels in the conditional ratio.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/ForwardSuffixLaw.suffix_after_prefix`
- Dependency: [D5/S3/Combinatorics/Graph/Queries/PartialForwardOrderLaw](PartialForwardOrderLaw.md)
