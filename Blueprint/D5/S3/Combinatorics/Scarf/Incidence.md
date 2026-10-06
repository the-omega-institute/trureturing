# An internal door has exactly two incident rooms

## Abstract

An internal door has exactly two incident rooms.

**Theorem 1.1 (An internal door has exactly two incident rooms).**

Lean statement: `D5/S3/Combinatorics/Scarf/Incidence.internal_door_two_rooms`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Scarf/Incidence.internal_door_two_rooms` (`✓ std3`). ∎

*Citation.* Math_XMUM (2025). *Brouwer fixed-point theorem via Scarf's lemma*. URL: <https://github.com/math-xmum/Brouwer/tree/f9dc162170e8711f78059a87edcd38ffc44a1bfb>.

*Commentary.*

For finite T and indexed linear orders, every internal door admits two distinct incident room pairs; every incident room equals one of them. The incidence relation includes both inserting a point and erasing an index.

The two colliding minimum indices give disjoint M sets. For each nonempty M set insert its actual maximal point; for an empty M set erase the corresponding index. All four branches construct distinct rooms and exclude every other incident room.

The result and proof source are attributed to Math_XMUM's MIT-licensed Brouwer repository at its immutable revision. No mathematical novelty is claimed. The combinatorics and real fixed-point argument establish no tetrahedral geometry, marked gluing, trajectory invariance, uniqueness, geometric Hessian, or convergence conclusion.

## References

- Truth anchor: `D5/S3/Combinatorics/Scarf/Incidence.internal_door_two_rooms`
- Dependency: [D5/S3/Combinatorics/Scarf/Dominance](Dominance.md)
