# Reduced Triangle Relations

## Abstract

Point potentials express relations among oriented triangle rows.

**Definition 1.1 (Normalized point potentials).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeOmissionRelations.IsOmissionPotential`

*Formalization.* `D5/S3/Combinatorics/Matroids/RankThreeOmissionRelations.IsOmissionPotential` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A potential vanishes at the chosen anchor, has zero total sum, and is killed by three at every point. It takes equal values at the ends of every pair in no omitted triple. Its values on each omitted triple sum to zero.

**Theorem 1.2 (Point potentials and relations).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeOmissionRelations.potential_to_relations_bijective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeOmissionRelations.potential_to_relations_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a finite indexed family on a finite ground set. Each triple has three distinct points, and triples with distinct indices share at most one point. Suppose multiplication by the ground-set size annihilates the coefficient group. For distinct root and anchor, evaluating a normalized potential by its difference across the first oriented edge of each triple gives a bijection with the reduced row relations.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeOmissionRelations.IsOmissionPotential`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeOmissionRelations.potential_to_relations_bijective`
