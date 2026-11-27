# Finite triangle moves on padded paths

## Abstract

Finite triangle moves on padded paths

**Theorem 1.1 (A finite family of edge-path comparisons has a common padding length).**

Lean statement: `D5/S3/Topology/FixedTargetGraphTermination.simultaneous_padded_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FixedTargetGraphTermination.simultaneous_padded_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

For a finite family of paths related by insertions and deletions across target triangles, choose a bound on every intermediate length. At any interval length above that bound, every admissible pair of endpoint-preserving paddings is connected by a common relative contiguity chain. Moving a repeated vertex frees the slot needed for a triangle insertion.

## References

- Truth anchor: `D5/S3/Topology/FixedTargetGraphTermination.simultaneous_padded_comparison`
- Dependency: [D5/S3/Topology/PathContiguity](PathContiguity.md)
