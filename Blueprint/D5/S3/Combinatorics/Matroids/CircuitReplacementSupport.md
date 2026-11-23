# Support of an Alternating Coordinate

## Abstract

Replacing one basis vector confines the change in an old alternating coefficient.

**Definition 1.1 (Coordinates read by an old coefficient).**

Lean statement: `D5/S3/Combinatorics/Matroids/CircuitReplacementSupport.oldCoordinateSupport`

*Formalization.* `D5/S3/Combinatorics/Matroids/CircuitReplacementSupport.oldCoordinateSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a selected index and a finite coordinate set, include the original set. If it contains the selected index, also include every same-size set obtained by replacing that index with one outside the original set.

**Theorem 1.2 (Disjoint replacement supports).**

Lean statement: `D5/S3/Combinatorics/Matroids/CircuitReplacementSupport.disjoint_old_coordinate_support`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/CircuitReplacementSupport.disjoint_old_coordinate_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two sets of equal size intersecting in at most their size minus two indices have disjoint replacement supports for any selected index.

**Theorem 1.3 (Transport of vanishing).**

Lean statement: `D5/S3/Combinatorics/Matroids/CircuitReplacementSupport.old_coordinate_zero_of_replacement_support`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/CircuitReplacementSupport.old_coordinate_zero_of_replacement_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two ordered bases agreeing away from the selected index, an old alternating coefficient vanishes if the new coefficients on its replacement support all vanish. Expansion in the one changed coordinate uses only these coefficients, because terms with repeated inputs vanish.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/CircuitReplacementSupport.disjoint_old_coordinate_support`
- Truth anchor: `D5/S3/Combinatorics/Matroids/CircuitReplacementSupport.oldCoordinateSupport`
- Truth anchor: `D5/S3/Combinatorics/Matroids/CircuitReplacementSupport.old_coordinate_zero_of_replacement_support`
- Dependency: [D5/S3/Combinatorics/Matroids/UniformCircuitResidueForms](UniformCircuitResidueForms.md)
