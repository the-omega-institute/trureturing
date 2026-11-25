# Seven Fano lines force at least seven link edges

## Abstract

Extending a tight Fano deletion

**Theorem 1.1 (A tight seven-point deletion forces degree at least seven).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FanoDeletion.q9_degree_ge_seven_of_fano_deletion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FanoDeletion.q9_degree_ge_seven_of_fano_deletion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a family of triples on eight points that places at least two triples in every five-set. If deleting a point leaves exactly seven triples, at least seven original triples contain that point.

The surviving triples form a Fano plane by the pair-incidence law. The complement of each line contains no surviving triple. Restoring the deleted point to that four-set therefore requires at least two link edges. Every pair belongs to exactly two line complements, since each of its points lies on three lines and their common line is unique. Counting incidences between link edges and line complements gives the bound.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FanoDeletion.q9_degree_ge_seven_of_fano_deletion`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SingletonFiveMask](Q9SingletonFiveMask.md)
