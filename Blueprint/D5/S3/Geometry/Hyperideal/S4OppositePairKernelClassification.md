# Exact S4 kernel for opposite pairings

## Abstract

The exact kernel of the finite action on the three opposite edge pairs.

For the displayed action of permutations of four vertices on the three opposite edge pairings, a permutation fixes every pair slot exactly when it is the identity or one of the three double swaps (01)(23), (02)(13), and (03)(12).

This classification supplies the missing exact-kernel step for the finite S4-to-three-pair interface. The existing action module supplies the bijectivity, six-element image, and explicit generator calculations; together they identify the finite quotient interface. No global geometric automorphism or extension to arbitrary face pairings is asserted.

**Theorem 1.1 (The four displayed permutations are exactly the kernel).**

Lean statement: `D5/S3/Geometry/Hyperideal/S4OppositePairKernelClassification.trivial_pair_action_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/S4OppositePairKernelClassification.trivial_pair_action_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite exhaustive proof classifies every permutation of the four vertices: fixing all three opposite pair slots is equivalent to being the identity or one of the three double swaps.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/S4OppositePairKernelClassification.trivial_pair_action_iff`
- Dependency: [D5/S3/Geometry/Hyperideal/S4OppositePairAction](S4OppositePairAction.md)
