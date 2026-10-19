# Rainbow colorings of a tetrahedron

## Abstract

Rainbow three-edge colorings of one tetrahedron are exactly the opposite-pair balanced colorings, with six named choices.

The six local edges are ordered (12,13,14,34,24,23). A color is an element of Fin 3. Each of the four faces is rainbow when its three edge colors are pairwise different.

**Theorem 1.1 (Local rainbow classification).**

Lean statement: `D5/S3/Geometry/Hyperideal/IridescentTetrahedronColoring.rainbow_iff_opposite_balanced_and_distinct`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/IridescentTetrahedronColoring.rainbow_iff_opposite_balanced_and_distinct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every six-edge coloring, all four faces are rainbow exactly when opposite pairs 12/34, 13/24, and 14/23 agree in color and the three pair colors are mutually different. The proof checks the finite three-color cases.

**Theorem 1.2 (Named rainbow realizations).**

Lean statement: `D5/S3/Geometry/Hyperideal/IridescentTetrahedronColoring.namedColoring_is_rainbow`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/IridescentTetrahedronColoring.namedColoring_is_rainbow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assigning a permutation of the three colors to the three opposite pairs produces a rainbow coloring on every face.

**Theorem 1.3 (Six named choices).**

Lean statement: `D5/S3/Geometry/Hyperideal/IridescentTetrahedronColoring.namedColoring_count`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/IridescentTetrahedronColoring.namedColoring_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The permutation group of the three colors has cardinality six, giving six named local choices.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/IridescentTetrahedronColoring.namedColoring_count`
- Truth anchor: `D5/S3/Geometry/Hyperideal/IridescentTetrahedronColoring.namedColoring_is_rainbow`
- Truth anchor: `D5/S3/Geometry/Hyperideal/IridescentTetrahedronColoring.rainbow_iff_opposite_balanced_and_distinct`
