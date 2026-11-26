# Graph distance under barycentric subdivision

## Abstract

Graph distance under barycentric subdivision

**Theorem 1.1 (Subdivision doubles the distance between subcomplexes).**

Lean statement: `D5/S3/Topology/BarycentricGraphDistance.subdivision_edist_eq_two_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/BarycentricGraphDistance.subdivision_edist_eq_two_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

The extended distance between the two subdivided subcomplexes is twice their original vertex-set distance. Bisecting a walk gives one inequality. A shortest walk in the subdivision alternates inclusions. Vertices chosen in consecutive inclusion minima share the intervening face and give the reverse inequality. The extended distance also treats empty endpoint sets and disconnected components.

**Theorem 1.2 (A full neighborhood persists at twice its radius).**

Lean statement: `D5/S3/Topology/BarycentricGraphDistance.mem_full_subcomplex_of_face_walk`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/BarycentricGraphDistance.mem_full_subcomplex_of_face_walk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Suppose a full subcomplex contains every original vertex within distance D of a given subcomplex. Then it contains each face reached from the given subcomplex by a walk of at most 2D edges in the subdivision graph. The first inclusion minimum of a shortest walk supplies a vertex close enough to the endpoint for every vertex of the starting face to reach the given subcomplex in D steps.

## References

- Truth anchor: `D5/S3/Topology/BarycentricGraphDistance.mem_full_subcomplex_of_face_walk`
- Truth anchor: `D5/S3/Topology/BarycentricGraphDistance.subdivision_edist_eq_two_mul`
