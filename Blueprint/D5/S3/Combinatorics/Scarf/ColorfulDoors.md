# A nearly colorful room has exactly two nearly colorful doors

## Abstract

A nearly colorful room has exactly two nearly colorful doors.

**Theorem 1.1 (A nearly colorful room has exactly two nearly colorful doors).**

Lean statement: `D5/S3/Combinatorics/Scarf/ColorfulDoors.doors_of_NCroom`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Scarf/ColorfulDoors.doors_of_NCroom` (`✓ std3`). ∎

*Citation.* Math_XMUM (2025). *Brouwer fixed-point theorem via Scarf's lemma*. URL: <https://github.com/math-xmum/Brouwer/tree/f9dc162170e8711f78059a87edcd38ffc44a1bfb>.

*Commentary.*

For arbitrary coloring c of the finite cell, a room missing exactly one color has a set of nearly colorful incident doors equal to a pair of distinct doors. No global injectivity of the coloring is assumed.

If the color image has full cell cardinality, construct an erased-point door and an inserted-color door using the unique external color. If the image has a one-unit deficit, erase either member of the collision pair and use three-collision exclusion to exhaust the doors.

The result and proof source are attributed to Math_XMUM's MIT-licensed Brouwer repository at its immutable revision. No mathematical novelty is claimed. The combinatorics and real fixed-point argument establish no tetrahedral geometry, marked gluing, trajectory invariance, uniqueness, geometric Hessian, or convergence conclusion.

## References

- Truth anchor: `D5/S3/Combinatorics/Scarf/ColorfulDoors.doors_of_NCroom`
- Dependency: [D5/S3/Combinatorics/Scarf/Incidence](Incidence.md)
