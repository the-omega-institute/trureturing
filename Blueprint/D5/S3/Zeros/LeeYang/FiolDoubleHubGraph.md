# Double-hub graph

## Abstract

The physical double-hub family: graph.

The centre joins the two hubs and each hub joins its own m leaves. The edge range has cardinality 2m+2, while the vertex type has cardinality 2m+3. Paths through the hubs and centre prove connectivity. The edge-count characterization of a finite tree then proves the actual support graph is a tree.

These new declarations are absent from the pinned statement-projection corpus. The supported omission records that projection gap; the mathematical argument and exact theorem statements are given in this document. No projection entry or judge is changed.

**Theorem 1.1 (nonloop).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubGraph.nonloop`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubGraph.nonloop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem nonloop (m : ℕ) (e : Edge m) : src e ≠ tgt e.

**Theorem 1.2 (actual tree).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubGraph.actual_tree`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubGraph.actual_tree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combines the explicitly constructed paths and edge bijection under the existing tree criterion. Exact source statement: theorem actual_tree (m : ℕ) : (graph m).IsTree.

## References

- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubGraph.actual_tree`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubGraph.nonloop`
- Dependency: [D5/S3/Zeros/LeeYang/FiolDoubleHubSource](FiolDoubleHubSource.md)
- Dependency: [D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation](QuiverTreeIsingRefutation.md)
