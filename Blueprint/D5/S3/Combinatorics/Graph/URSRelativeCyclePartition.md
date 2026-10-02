# Invariant partitions of relative moved support

## Abstract

Actual reflected incidences restrict every invariant partition of the moved support of two relative rows. All fibres and joint counts use one indexed array.

**Definition 1.1 (Relative row coordinates).**

Lean statement: `D5/S3/Combinatorics/Graph/URSRelativeCyclePartition.relative`

*Formalization.* `D5/S3/Combinatorics/Graph/URSRelativeCyclePartition.relative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The relative permutation of row t with respect to row r is rho(r) inverse composed with rho(t). It acts on the original column set and retains all actual row indices.

**Definition 1.2 (Moved support).**

Lean statement: `D5/S3/Combinatorics/Graph/URSRelativeCyclePartition.movedSupport`

*Formalization.* `D5/S3/Combinatorics/Graph/URSRelativeCyclePartition.movedSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The moved support D contains exactly those original columns not fixed by the relative permutation of rows r and s.

**Theorem 1.3 (The invariant partition bound).**

Lean statement: `D5/S3/Combinatorics/Graph/URSRelativeCyclePartition.actual_invariant_moved_support_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/URSRelativeCyclePartition.actual_invariant_moved_support_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Enrico Iurlano, Günther R. Raidl (2026). *Pairwise Reflection Symmetry in Generalized Latin Rectangles*. DOI: [10.48550/arXiv.2606.28315](https://doi.org/10.48550/arXiv.2606.28315). URL: <https://arxiv.org/html/2606.28315v1>.

*Commentary.*

Let n be odd and at least three. An indexed family of 2n permutations on Fin n has actual column-symbol fibres of size two, and equal joint counts for reflected patterns whenever their columns and symbols are distinct. Choose distinct row indices r,s and let sigma be rho(r) inverse composed with rho(s). For any subset U of its moved support D with sigma(U)=U, put V=D minus U. Then n+|D| is at most |U| squared plus |V| squared plus one. Either block may be empty; commutation, sorting, identity-first and distinct-permutation assumptions are unnecessary.

Saturation makes the entries of every third row that remain in the agreement set form fixed-point-free transpositions. Its actual D-to-D count is consequently odd. Original reflected incidences also force each two-step segment through the agreement set to return to its source or to its sigma-image. Contracting these segments gives a genuine permutation of D whose crossing edges between U and V are all uncontracted and occur equally in both directions. Each third row therefore has an odd positive actual within-block count.

The actual fibre frequencies give total within-block count 2(|U| squared plus |V| squared). Rows r and s contribute |D| each, while the remaining 2n-2 rows contribute at least one each. Double counting proves the bound. This restriction alone does not settle bipartiteness of the fibre graph.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/URSRelativeCyclePartition.actual_invariant_moved_support_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/URSRelativeCyclePartition.movedSupport`
- Truth anchor: `D5/S3/Combinatorics/Graph/URSRelativeCyclePartition.relative`
- Dependency: [D5/S3/Combinatorics/Graph/URSComponentParity](URSComponentParity.md)
