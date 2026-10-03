# Mostow--Prasad descent through orbit quotients

## Abstract

Conjugate isometric actions descend to an equivalence of orbit quotients.

This module supplies the quotient-side bridge for holonomy rigidity. It is independent of the hyperbolic lattice theorem: once a group isomorphism is implemented by a chosen ambient isometry, that isometry descends to the corresponding orbit quotients.

**Definition 1.1 (Orbit relation of an isometric representation).**

Lean statement: `D5/S3/Geometry/MostowPrasadDescent.orbitSetoid`

*Formalization.* `D5/S3/Geometry/MostowPrasadDescent.orbitSetoid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

orbitSetoid identifies points related by one element of the represented group.

**Definition 1.2 (Orbit quotient).**

Lean statement: `D5/S3/Geometry/MostowPrasadDescent.OrbitQuotient`

*Formalization.* `D5/S3/Geometry/MostowPrasadDescent.OrbitQuotient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

OrbitQuotient is the set-theoretic quotient by the representation orbit relation.

**Theorem 1.3 (Orbit-related points have equal quotient classes).**

Lean statement: `D5/S3/Geometry/MostowPrasadDescent.orbitQuotientMk_eq_of_orbit`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/MostowPrasadDescent.orbitQuotientMk_eq_of_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical projection identifies any two points related by the represented group.

**Definition 1.4 (Isometric group conjugacy).**

Lean statement: `D5/S3/Geometry/MostowPrasadDescent.IsometricGroupConjugacy`

*Formalization.* `D5/S3/Geometry/MostowPrasadDescent.IsometricGroupConjugacy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A group isomorphism is implemented by a chosen isometry conjugating the two representations.

**Definition 1.5 (Descended quotient map).**

Lean statement: `D5/S3/Geometry/MostowPrasadDescent.descendedMap`

*Formalization.* `D5/S3/Geometry/MostowPrasadDescent.descendedMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The chosen conjugator gives a well-defined map from the first orbit quotient to the second.

**Definition 1.6 (Descended inverse map).**

Lean statement: `D5/S3/Geometry/MostowPrasadDescent.descendedInverse`

*Formalization.* `D5/S3/Geometry/MostowPrasadDescent.descendedInverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse conjugator gives the reverse quotient map.

**Theorem 1.7 (Equivalence of orbit quotients).**

Lean statement: `D5/S3/Geometry/MostowPrasadDescent.descendedEquiv`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/MostowPrasadDescent.descendedEquiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The descended map and its inverse form an equivalence of the two orbit quotients.

**Theorem 1.8 (The descended map commutes with the quotient projection).**

Lean statement: `D5/S3/Geometry/MostowPrasadDescent.descendedMap_comp_orbitQuotientMk`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/MostowPrasadDescent.descendedMap_comp_orbitQuotientMk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On every representative point, the quotient map is exactly induced by the ambient conjugator.

**Theorem 1.9 (The quotient equivalence commutes with the projection).**

Lean statement: `D5/S3/Geometry/MostowPrasadDescent.descendedEquiv_comp_orbitQuotientMk`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/MostowPrasadDescent.descendedEquiv_comp_orbitQuotientMk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equivalence has the expected representative-level formula.

## References

- Truth anchor: `D5/S3/Geometry/MostowPrasadDescent.IsometricGroupConjugacy`
- Truth anchor: `D5/S3/Geometry/MostowPrasadDescent.OrbitQuotient`
- Truth anchor: `D5/S3/Geometry/MostowPrasadDescent.descendedEquiv`
- Truth anchor: `D5/S3/Geometry/MostowPrasadDescent.descendedEquiv_comp_orbitQuotientMk`
- Truth anchor: `D5/S3/Geometry/MostowPrasadDescent.descendedInverse`
- Truth anchor: `D5/S3/Geometry/MostowPrasadDescent.descendedMap`
- Truth anchor: `D5/S3/Geometry/MostowPrasadDescent.descendedMap_comp_orbitQuotientMk`
- Truth anchor: `D5/S3/Geometry/MostowPrasadDescent.orbitQuotientMk_eq_of_orbit`
- Truth anchor: `D5/S3/Geometry/MostowPrasadDescent.orbitSetoid`
- Dependency: [D5/S3/Geometry/MostowPrasadRigidity](MostowPrasadRigidity.md)
