# Half-edge coordinates on a subdivided graph

## Abstract

Half-edge coordinates on a subdivided graph

**Theorem 1.1 (The distance to the midpoint has a common global realization on a graph).**

Lean statement: `D5/S3/Topology/GraphSubdivisionHalves.split_charts`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/GraphSubdivisionHalves.split_charts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Assign each subdivided half-edge to its old endpoint and leave the midpoint unassigned. The assignments agree wherever edge charts meet. Every face has at most one assigned endpoint among its vertices, and distances from the midpoints vary by at most one along an edge. An isolated old vertex receives the same coordinate as an old endpoint.

## References

- Truth anchor: `D5/S3/Topology/GraphSubdivisionHalves.split_charts`
- Dependency: [D5/S3/Topology/GraphSubdivisionIntervals](GraphSubdivisionIntervals.md)
