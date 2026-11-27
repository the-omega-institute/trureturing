# Relative contiguity by descending rank

## Abstract

Relative contiguity by descending rank

**Theorem 1.1 (Bounded ranked interpolation).**

Lean statement: `D5/S3/Topology/DescendingClosureContiguity.exists_relative_contiguity_of_le`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/DescendingClosureContiguity.exists_relative_contiguity_of_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

For order maps f and g with g pointwise below f, suppose the source poset has a strictly increasing natural rank bounded by n. At stage k use g on vertices of rank less than k and f on the others. The stages are order maps from f at index zero to g at index n+1, stay above g, and fix every vertex on which f and g agree. The union of adjacent stage images of any chain is a chain.

**Theorem 1.2 (Relative deformation of a face neighborhood).**

Lean statement: `D5/S3/Topology/DescendingClosureContiguity.face_neighborhood_relative_contiguity`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/DescendingClosureContiguity.face_neighborhood_relative_contiguity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

For a complex on a finite vertex type V with decidable equality and a selected vertex set S, take the poset of nonempty faces meeting S. Intersection with S is a descending order map. Face cardinality gives a rank, so the identity reaches this map at index card(V)+1 through contiguous order-complex maps fixing every face contained in S.

**Theorem 1.3 (Two vertex subsets cover the face flags).**

Lean statement: `D5/S3/Topology/DescendingClosureContiguity.two_subsets_cover_face_flags`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/DescendingClosureContiguity.two_subsets_cover_face_flags` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

If two finite vertex subsets cover V, then each chain of nonempty faces lies entirely in one of their face-poset neighborhoods. For a nonempty chain choose a least face by cardinality and a vertex in that face. Every larger face meets the same selected subset.

**Theorem 1.4 (Contiguous vertex maps induce a face-poset contiguity chain).**

Lean statement: `D5/S3/Topology/DescendingClosureContiguity.faceImage_connected_by_contiguity`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/DescendingClosureContiguity.faceImage_connected_by_contiguity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

For complexes K and L, let the source vertex type be finite and the target vertex type have decidable equality. Suppose f and g map every face of K to a face of L, with the union of the two images also a face of L. The union gives a common containing order map of face posets. Applying ranked interpolation from that map to each induced face-image map yields a finite chain of contiguous order-complex maps joining the two induced maps.

## References

- Truth anchor: `D5/S3/Topology/DescendingClosureContiguity.exists_relative_contiguity_of_le`
- Truth anchor: `D5/S3/Topology/DescendingClosureContiguity.faceImage_connected_by_contiguity`
- Truth anchor: `D5/S3/Topology/DescendingClosureContiguity.face_neighborhood_relative_contiguity`
- Truth anchor: `D5/S3/Topology/DescendingClosureContiguity.two_subsets_cover_face_flags`
