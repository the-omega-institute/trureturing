# Distance matrices along cotree component cuts

## Abstract

Distance matrices along cotree component cuts.

**Definition 1.1 (Ordinary distance matrix).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.distanceMatrix`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.distanceMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Cast the native shortest-path distances to real numbers.

**Definition 1.2 (All-ones matrix).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.ones`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.ones` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Every entry is one, including the diagonal.

**Theorem 1.3 (Native distances).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.dist_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.dist_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Distinct vertices of a connected cograph have distance one on edges and two on nonedges. The diagonal is zero.

**Theorem 1.4 (Distance matrix identity).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.distanceMatrix_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.distanceMatrix_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

The ordinary distance matrix is 2J − 2I − A.

**Definition 1.5 (Local shifted matrix).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localMatrix`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

The local matrix is (2−q)J − (x+2)I − A on the induced graph at shift x and parent label q.

**Theorem 1.6 (Shifted root distance matrix).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localMatrix_root`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localMatrix_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

At q=0 on a connected cograph the local matrix is the shifted ordinary distance matrix.

**Theorem 1.7 (Restriction to a child).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localMatrix_induce`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localMatrix_induce` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Restricting the local matrix to an induced carrier uses the same shift and label with the child adjacency matrix.

**Definition 1.8 (Numerical labels).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.label`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.label` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

One represents a join and two represents a union.

**Definition 1.9 (Coordinates for component cuts).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.componentEquiv`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.componentEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Each vertex corresponds to a component of the cut and a vertex in its support.

**Theorem 1.10 (Block expression).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localMatrix_node`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localMatrix_node` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

The parent matrix consists of the child blocks and the all-ones update with coefficient given by the label difference.

**Definition 1.11 (Local linear operator).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localOperator`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localOperator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

View the local matrix as an endomorphism of the real Euclidean space of native vertices.

**Definition 1.12 (All-ones vector).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.oneVector`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.oneVector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

All coordinates are one.

**Theorem 1.13 (Pairing with all ones).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.pairing_oneVector`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.pairing_oneVector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Pairing with the all-ones vector sums the coordinates.

**Theorem 1.14 (Symmetry of the local operator).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localOperator_symmetric`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localOperator_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

The adjacency matrix is symmetric, as are the identity and all-ones terms.

**Definition 1.15 (Euclidean component coordinates).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.componentCoordinates`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.componentCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Separate the native Euclidean space into a product indexed by cut components.

**Theorem 1.16 (Rank-one update at a node).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localOperator_node`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localOperator_node` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

In component coordinates apply the child block operator and a rank-one update in the direction of the all-ones vector.

**Theorem 1.17 (Transport of local states).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localOperator_node_states`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localOperator_node_states` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Component coordinates preserve nullity, nonzero kernel pairing and scalar response under the block expression.

**Theorem 1.18 (Leaf states).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.leaf_states`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.leaf_states` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

The one-dimensional leaf gives a nonzero kernel sum at its pole and a scalar response at other shifts.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.componentCoordinates`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.componentEquiv`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.dist_eq`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.distanceMatrix`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.distanceMatrix_eq`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.label`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.leaf_states`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localMatrix`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localMatrix_induce`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localMatrix_node`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localMatrix_root`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localOperator`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localOperator_node`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localOperator_node_states`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.localOperator_symmetric`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.oneVector`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.ones`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.pairing_oneVector`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree](NormalizedCographCotree.md)
- Dependency: [D5/S3/QuadraticForms/SymmetricRankOneKernel](../../QuadraticForms/SymmetricRankOneKernel.md)
