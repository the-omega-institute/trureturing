# Labelled Steiner Switch Counts from Central Returns

## Abstract

Prescribed component returns give a count of starts in a labelled triple system.

**Theorem 1.1 (Realizing a prescribed switch count on finite labels).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerSchreierSwitchCount.realizeLabelledSwitchCount`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerSchreierSwitchCount.realizeLabelledSwitchCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Falcone, Ágota Figula, Mario Galici (2025). *Extensions of Steiner Triple Systems*. DOI: [10.1002/jcd.21964](https://doi.org/10.1002/jcd.21964). URL: <https://arxiv.org/abs/2406.12796>.

*Commentary.*

Fix a finite centreless Steiner loop, two distinct nonidentity pivots, and a finite abelian group of exponent at most two. The graph records the two pivot matchings. Prescribe a return on each connected component other than the component of the identity.

The theorem labels the extension so the adjoined option point is its identity. It gives the deleted label and the retained pivot corresponding to the two given pivots, a complete Steiner triple system, and its matching of uncovered pairs after deletion.

A successful starting label corresponds exactly to a point where the two matching translations have unequal endpoints in the two possible orders. This is equivalent to failing to return after two rounds. The eligible quotient points are those that fail to return after two rounds or belong to a nonidentity component with nonzero prescribed return. Every eligible quotient point contributes its full fibre, whose size is the order of the additive group.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerSchreierSwitchCount.realizeLabelledSwitchCount`
- Dependency: [D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches](SteinerAlternatingSwitches.md)
- Dependency: [D5/S3/Combinatorics/Matroids/SteinerSchreierExtension](SteinerSchreierExtension.md)
