# Normalized cotrees on native graph vertices

## Abstract

Normalized cotrees on native graph vertices.

**Definition 1.1 (Graph to cut).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.cutGraph`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.cutGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

A union splits by graph components and a join splits by complement components.

**Definition 1.2 (Normalized cotree).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.Cotree`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.Cotree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Leaves have singleton carriers. Internal nodes use native induced component graphs and alternate the union and join labels.

**Definition 1.3 (Root label).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.rootKind`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.rootKind` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

The label distinguishes a singleton, a union and a join.

**Theorem 1.4 (Complement components).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.not_connected_compl_of_not_induced_pathFour`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.not_connected_compl_of_not_induced_pathFour` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

The complement of a finite connected nontrivial cograph is disconnected.

**Theorem 1.5 (Existence of a normalized cotree).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.exists_cotree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.exists_cotree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Recurse on the strict decrease in carrier cardinality along graph and complement component cuts.

**Theorem 1.6 (Cross edges).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.adj_iff_join_of_component_ne`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.adj_iff_join_of_component_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Distinct components of the cut are completely adjacent at a join and completely nonadjacent at a union.

**Theorem 1.7 (Internal support).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.nontrivial_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.nontrivial_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

A subtree has a nontrivial carrier exactly when it has an internal root.

**Theorem 1.8 (Universal vertices).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.universal_iff_leaf_child`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.universal_iff_leaf_child` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

At a join, the universal vertices are precisely those in leaf children.

**Theorem 1.9 (Join root).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.exists_join_root`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.exists_join_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

A nontrivial connected cograph has a normalized cotree with join at its root.

**Theorem 1.10 (Leaf width).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.width_leaf`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.width_leaf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Each singleton subtree has width one.

**Theorem 1.11 (Width at an internal node).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.width_node`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.width_node` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Take the maximum of one and the sum of the widths of the nonleaf children.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.Cotree`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.adj_iff_join_of_component_ne`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.cutGraph`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.exists_cotree`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.exists_join_root`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.nontrivial_iff`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.not_connected_compl_of_not_induced_pathFour`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.rootKind`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.universal_iff_leaf_child`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.width_leaf`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.width_node`
- Dependency: [D5/S3/Combinatorics/Graph/Cographs/CographSeinsche](../Graph/Cographs/CographSeinsche.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth](CographVicinalWidth.md)
