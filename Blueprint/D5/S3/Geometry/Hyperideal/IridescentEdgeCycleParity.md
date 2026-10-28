# Parity from transported rainbow endpoint colors

## Abstract

A finite normal-edge cycle with a transported pair of distinct non-target colors has even length.

A RainbowCycle consists of a finite set of occurrences, a successor permutation, and two colors recorded from the chosen endpoint of a target edge. The two colors are distinct at every occurrence, and the successor exchanges the two colors.

**Theorem 1.1 (Transported endpoint colors force even length).**

Lean statement: `D5/S3/Geometry/Hyperideal/IridescentEdgeCycleParity.even_card_of_rainbow_cycle`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/IridescentEdgeCycleParity.even_card_of_rainbow_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ordering the two distinct colors gives a Boolean orientation. The successor reverses this orientation. Choosing the successor in one orientation and its inverse in the other produces a fixed-point-free involution, so the finite occurrence set has even cardinality.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/IridescentEdgeCycleParity.even_card_of_rainbow_cycle`
- Dependency: [D5/S3/PrimeForms/Crossing/GlideCrossingParity](../../PrimeForms/Crossing/GlideCrossingParity.md)
