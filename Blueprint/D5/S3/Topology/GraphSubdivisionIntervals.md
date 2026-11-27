# Intervals in ordinary graph subdivisions

## Abstract

Intervals in ordinary graph subdivisions

**Theorem 1.1 (Every oriented edge has an interval chart of length two to the subdivision depth).**

Lean statement: `D5/S3/Topology/GraphSubdivisionIntervals.graph_subdivision_intervals_oriented`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/GraphSubdivisionIntervals.graph_subdivision_intervals_oriented` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

A subdivision replaces each path segment by two. Singleton faces and edge faces give the even and odd coordinates. At every depth the chart describes the entire subdivided edge, its endpoints are the retained old vertices, and interior vertices belong to just one chart. Every subdivided face is in a chart or is an isolated old vertex.

## References

- Truth anchor: `D5/S3/Topology/GraphSubdivisionIntervals.graph_subdivision_intervals_oriented`
- Dependency: [D5/S3/Geometry/FiniteAlexanderDualCollapse](../Geometry/FiniteAlexanderDualCollapse.md)
- Dependency: [D5/S3/Topology/PathContiguity](PathContiguity.md)
