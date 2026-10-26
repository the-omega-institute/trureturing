# Rooted original-geodesic geometry

## Abstract

Original-host mutual visibility and the auxiliary geometry of the full mixed reconfiguration graph.

**Definition 1.1 (Mandatory original geodesics).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/Geodesics.Mandatory`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/Geodesics.Mandatory` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

A vertex is mandatory between two endpoints when every original-host walk attaining their distance contains it. This universal relation is used only as auxiliary geometry; source visibility remains existential.

**Definition 1.2 (Strict ancestry towards one root).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/Geodesics.Dominates`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/Geodesics.Dominates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

The nearer vertex is distinct from the root and from the farther vertex and is mandatory on every shortest path from the farther vertex to the root. Distance additivity makes its root distance strictly smaller.

**Theorem 1.3 (Inward replacement of a visible common-neighbor triple).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/Geodesics.inward_replacement`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/Geodesics.inward_replacement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

Let the host be connected, let u strictly dominate v towards w, let y be adjacent to both u and v, and let p be adjacent to u with root distance one less than u. If the original triple u,v,y is visible, then p differs from v and y. There are configurations Q with labels p,v,y and P with labels p,y, an actual-host-edge slide from the original triple to Q, and a token removal from Q to P. The root-distance sum of the terminal pair is strictly smaller than that of u,v. The proof first forces the height of y and the exact distances from p to y and v, then builds existential geodesic witnesses from the predecessor edge and the original visible triple.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Geodesics.Dominates`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Geodesics.Mandatory`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Geodesics.inward_replacement`
- Dependency: [D5/S3/Combinatorics/Graph/MutualVisibility/Model](Model.md)
