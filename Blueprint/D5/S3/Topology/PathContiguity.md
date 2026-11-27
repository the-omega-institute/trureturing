# Relative contiguity of maps to an interval

## Abstract

Relative contiguity of maps to an interval

**Theorem 1.1 (Maps to a subdivided interval are contiguous relative to shared values).**

Lean statement: `D5/S3/Topology/PathContiguity.relative_complex_contiguity`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/PathContiguity.relative_complex_contiguity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Take the pointwise minimum of two interval-valued maps. From either map, lower a vertex whose current label is maximal among those still above the minimum. No neighbour has a higher label, so one decrease preserves contiguity on every incident simplex. The sum of labels decreases and vertices where the maps agree keep their value.

## References

- Truth anchor: `D5/S3/Topology/PathContiguity.relative_complex_contiguity`
- Dependency: [D5/S3/Topology/BarycentricBaseRigidity](BarycentricBaseRigidity.md)
