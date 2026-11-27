# Contraction of a graph map after subdividing its source

## Abstract

Contraction of a graph map after subdividing its source

**Theorem 1.1 (Finite edge-path witnesses suffice for a contiguity contraction in a fixed target).**

Lean statement: `D5/S3/Topology/GraphSubdivisionNullhomotopy.supported_graph_map_contracts`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/GraphSubdivisionNullhomotopy.supported_graph_map_contracts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

For a map from a finite graph to a simplicial complex, choose a path from one target base vertex to each old vertex image. Suppose that on each oriented edge, the mapped edge is equivalent by triangle moves to the reverse of the first path followed by the second. Then beyond a common ordinary subdivision depth, every choice of a vertex in each original support gives a map contiguous through a finite chain to the base vertex. Parametrize each subdivided edge by an interval, replace its map by the two paths through the midpoint while fixing the endpoints, and contract the half paths together.

## References

- Truth anchor: `D5/S3/Topology/GraphSubdivisionNullhomotopy.supported_graph_map_contracts`
- Dependency: [D5/S3/Topology/FixedTargetGraphTermination](FixedTargetGraphTermination.md)
- Dependency: [D5/S3/Topology/GraphSubdivisionHalves](GraphSubdivisionHalves.md)
- Dependency: [D5/S3/Topology/GraphSubdivisionIntervals](GraphSubdivisionIntervals.md)
