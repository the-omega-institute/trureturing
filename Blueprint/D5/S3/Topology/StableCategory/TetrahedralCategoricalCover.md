# A two-piece stable categorical cover in dimension three

## Abstract

A two-piece stable categorical cover in dimension three

**Theorem 1.1 (A relative two-piece cover by face neighborhoods).**

Lean statement: `D5/S3/Topology/StableCategory/TetrahedralCategoricalCover.two_meeting_face_pieces_of_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/TetrahedralCategoricalCover.two_meeting_face_pieces_of_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Let a nonempty finite subcomplex have a proper four-rank coloring and a nullhomotopic realization inclusion in a finite ambient complex with connected one-skeleton. At a common ordinary subdivision depth, it admits a cover by two subcomplexes whose maps into the subdivided ambient lie in the contiguity class of constants.

The nullhomotopy restricts to both rank graphs. The tetrahedral refinement gives two categorical induced regions. In one further subdivision, intersecting each face with the selected region gives a face map below the ambient inclusion. Every flag belongs to the neighborhood selected by a vertex of its least face.

**Theorem 1.2 (Two categorical lower sets after ordinary subdivision).**

Lean statement: `D5/S3/Topology/StableCategory/TetrahedralCategoricalCover.two_lower_sets_of_contractible_order_complex`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/TetrahedralCategoricalCover.two_lower_sets_of_contractible_order_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Let a finite poset have order-complex dimension at most three. An actual contraction of its order-complex realization gives a cover by two categorical lower sets after finitely many ordinary subdivisions.

The heights of the poset elements give four ranks. Pairing ranks gives two bipartite graphs. Repeated tetrahedral refinements subdivide each parameter graph four times for every three ambient subdivisions. Fixed-target graph contractions then apply through the original edge carriers, and the face-meeting construction transfers the two induced regions to lower sets.

## References

- Truth anchor: `D5/S3/Topology/StableCategory/TetrahedralCategoricalCover.two_lower_sets_of_contractible_order_complex`
- Truth anchor: `D5/S3/Topology/StableCategory/TetrahedralCategoricalCover.two_meeting_face_pieces_of_rank`
- Dependency: [D5/S3/Geometry/FiniteConeUnionWedge](../../Geometry/FiniteConeUnionWedge.md)
