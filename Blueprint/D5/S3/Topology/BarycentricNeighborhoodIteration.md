# Graph neighborhoods after iterated subdivision

## Abstract

Graph neighborhoods after iterated subdivision

**Theorem 1.1 (Full subcomplexes retain graph neighborhoods at every depth).**

Lean statement: `D5/S3/Topology/BarycentricNeighborhoodIteration.containsBall_iteratedSubdivision`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/BarycentricNeighborhoodIteration.containsBall_iteratedSubdivision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Let a full subcomplex W contain every ambient vertex within graph distance D of P. After r ordinary barycentric subdivisions, the subdivided W contains every vertex within distance D times two to the power r of the subdivided P. The proof identifies the subdivided edges with comparable faces and reapplies the face-walk estimate because the subdivided W is full.

## References

- Truth anchor: `D5/S3/Topology/BarycentricNeighborhoodIteration.containsBall_iteratedSubdivision`
- Dependency: [D5/S3/Topology/BarycentricGraphDistance](BarycentricGraphDistance.md)
