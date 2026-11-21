# Induced four-vertex paths and the Seinsche cut

## Abstract

Induced four-vertex paths and the Seinsche cut.

**Definition 1.1 (Induced four-vertex path exclusion).**

Lean statement: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.IsP4Free`

*Formalization.* `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.IsP4Free` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

No four distinct vertices induce exactly the three successive edges of a path.

**Theorem 1.2 (Pullback).**

Lean statement: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.comap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.comap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Pulling back the graph along a map preserves induced four-vertex path exclusion.

**Theorem 1.3 (Induced subgraphs).**

Lean statement: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.induce`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.induce` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Restricting to a vertex subset preserves induced four-vertex path exclusion.

**Theorem 1.4 (Complementation).**

Lean statement: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.compl`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.compl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

The four-vertex path is self-complementary, so its absence is preserved by complementation.

**Theorem 1.5 (Path exclusion).**

Lean statement: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.not_pathGraph_four_isIndContained`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.not_pathGraph_four_isIndContained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

The four-vertex condition excludes the native induced path graph.

**Theorem 1.6 (Induced path construction).**

Lean statement: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.pathGraph_four_isIndContained_of_adj`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.pathGraph_four_isIndContained_of_adj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

The three successive edges and the required nonedges on four distinct vertices give an induced path embedding.

**Theorem 1.7 (Equivalent path definitions).**

Lean statement: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.isP4Free_iff_not_pathGraph_four_isIndContained`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.isP4Free_iff_not_pathGraph_four_isIndContained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

The explicit four-vertex condition and the native induced-embedding exclusion are equivalent.

**Theorem 1.8 (Neighbors of a deleted vertex).**

Lean statement: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.exists_neighbor_in_deleted_component`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.exists_neighbor_in_deleted_component` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

In a preconnected graph each component left after deleting a vertex contains one of its neighbors.

**Theorem 1.9 (Adjacency inside a deleted component).**

Lean statement: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.adj_of_deleted_reachable`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.adj_of_deleted_reachable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

If the deleted vertex has a neighbor outside a deleted component and a neighbor inside it, it is adjacent throughout that component.

**Theorem 1.10 (Completeness to deleted components).**

Lean statement: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.adj_all_of_not_preconnected_delete`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.adj_all_of_not_preconnected_delete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

If deleting a vertex disconnects a preconnected cograph, that vertex is adjacent to every other vertex.

**Theorem 1.11 (Universal vertex in the complement).**

Lean statement: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.not_preconnected_compl_of_universal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.not_preconnected_compl_of_universal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

On a nontrivial carrier the complement of a graph with a universal vertex is disconnected.

**Theorem 1.12 (Induction and complementation).**

Lean statement: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.compl_induce_eq_induce_compl`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.compl_induce_eq_induce_compl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Taking the complement commutes with restricting to a vertex subset.

**Theorem 1.13 (Seinsche decomposition).**

Lean statement: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.not_preconnected_or_compl`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.not_preconnected_or_compl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

On a finite nontrivial path-free carrier, the graph or its complement fails preconnectedness.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.IsP4Free`
- Truth anchor: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.adj_all_of_not_preconnected_delete`
- Truth anchor: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.adj_of_deleted_reachable`
- Truth anchor: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.comap`
- Truth anchor: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.compl`
- Truth anchor: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.compl_induce_eq_induce_compl`
- Truth anchor: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.exists_neighbor_in_deleted_component`
- Truth anchor: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.induce`
- Truth anchor: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.isP4Free_iff_not_pathGraph_four_isIndContained`
- Truth anchor: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.not_pathGraph_four_isIndContained`
- Truth anchor: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.not_preconnected_compl_of_universal`
- Truth anchor: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.not_preconnected_or_compl`
- Truth anchor: `D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.pathGraph_four_isIndContained_of_adj`
