# Mostow--Prasad rigidity: metric and group interfaces

## Abstract

The metric and group-conjugacy interfaces for the Mostow--Prasad rigidity endpoint.

The reusable interfaces for the Mostow--Prasad endpoint include metric uniqueness and the algebraic statement that holonomy representations are related by conjugacy in an ambient group. The full theorem requires additional hyperbolic geometry and is not claimed by this module.

**Theorem 1.1 (Dense-set uniqueness of isometries).**

Lean statement: `D5/S3/Geometry/MostowPrasadRigidity.isometry_equiv_eq_of_eqOn_dense`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/MostowPrasadRigidity.isometry_equiv_eq_of_eqOn_dense` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two isometry equivalences that agree on a dense subset of the source are equal.

**Theorem 1.2 (Dense-range uniqueness).**

Lean statement: `D5/S3/Geometry/MostowPrasadRigidity.isometry_equiv_eq_of_dense_range`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/MostowPrasadRigidity.isometry_equiv_eq_of_dense_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same uniqueness result accepts a dense parametrization directly.

**Definition 1.3 (Existence of an isometry representative).**

Lean statement: `D5/S3/Geometry/MostowPrasadRigidity.HasIsometryRepresentative`

*Formalization.* `D5/S3/Geometry/MostowPrasadRigidity.HasIsometryRepresentative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A homotopy equivalence has an isometry representative.

**Definition 1.4 (Uniqueness of an isometry representative).**

Lean statement: `D5/S3/Geometry/MostowPrasadRigidity.UniqueIsometryRepresentative`

*Formalization.* `D5/S3/Geometry/MostowPrasadRigidity.UniqueIsometryRepresentative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All isometry representatives in one homotopy class are equal.

**Definition 1.5 (Mostow--Prasad endpoint specification).**

Lean statement: `D5/S3/Geometry/MostowPrasadRigidity.MostowPrasadRigidityEndpoint`

*Formalization.* `D5/S3/Geometry/MostowPrasadRigidity.MostowPrasadRigidityEndpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every homotopy equivalence has a unique isometry representative.

**Theorem 1.6 (An isometry supplies its representative).**

Lean statement: `D5/S3/Geometry/MostowPrasadRigidity.hasIsometryRepresentative_of_isometry`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/MostowPrasadRigidity.hasIsometryRepresentative_of_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An isometry induces a homotopy equivalence for which it is a representative.

**Theorem 1.7 (Dense boundary criterion for uniqueness).**

Lean statement: `D5/S3/Geometry/MostowPrasadRigidity.uniqueIsometryRepresentative_of_eqOn_dense`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/MostowPrasadRigidity.uniqueIsometryRepresentative_of_eqOn_dense` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Agreement on a dense boundary set proves uniqueness of representatives.

**Theorem 1.8 (Endpoint from existence and uniqueness).**

Lean statement: `D5/S3/Geometry/MostowPrasadRigidity.existsUnique_isometryRepresentative_of_parts`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/MostowPrasadRigidity.existsUnique_isometryRepresentative_of_parts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existence and uniqueness obligations combine into the exact endpoint.

**Definition 1.9 (Group conjugacy interface).**

Lean statement: `D5/S3/Geometry/MostowPrasadRigidity.GroupConjugacy`

*Formalization.* `D5/S3/Geometry/MostowPrasadRigidity.GroupConjugacy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An abstract group isomorphism is realized by conjugacy in an ambient group.

**Theorem 1.10 (Symmetry of group conjugacy).**

Lean statement: `D5/S3/Geometry/MostowPrasadRigidity.groupConjugacy_symm`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/MostowPrasadRigidity.groupConjugacy_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The group-conjugacy relation is preserved by inverting the group isomorphism.

**Theorem 1.11 (Composition of group conjugacy).**

Lean statement: `D5/S3/Geometry/MostowPrasadRigidity.groupConjugacy_trans`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/MostowPrasadRigidity.groupConjugacy_trans` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugacy certificates compose along group isomorphisms.

**Theorem 1.12 (Uniqueness of the conjugator).**

Lean statement: `D5/S3/Geometry/MostowPrasadRigidity.groupConjugacy_conjugator_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/MostowPrasadRigidity.groupConjugacy_conjugator_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A trivial centralizer for the holonomy image makes the ambient conjugator unique.

**Definition 1.13 (Dense holonomy orbit).**

Lean statement: `D5/S3/Geometry/MostowPrasadRigidity.DenseOrbit`

*Formalization.* `D5/S3/Geometry/MostowPrasadRigidity.DenseOrbit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The orbit of a chosen basepoint under an isometry representation is dense.

**Theorem 1.14 (Dense orbit centralizer criterion).**

Lean statement: `D5/S3/Geometry/MostowPrasadRigidity.rangeCentralizerTrivial_of_dense_orbit`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/MostowPrasadRigidity.rangeCentralizerTrivial_of_dense_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A dense orbit and basepoint control imply a trivial centralizer.

## References

- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.DenseOrbit`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.GroupConjugacy`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.HasIsometryRepresentative`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.MostowPrasadRigidityEndpoint`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.UniqueIsometryRepresentative`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.existsUnique_isometryRepresentative_of_parts`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.groupConjugacy_conjugator_unique`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.groupConjugacy_symm`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.groupConjugacy_trans`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.hasIsometryRepresentative_of_isometry`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.isometry_equiv_eq_of_dense_range`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.isometry_equiv_eq_of_eqOn_dense`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.rangeCentralizerTrivial_of_dense_orbit`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.uniqueIsometryRepresentative_of_eqOn_dense`
