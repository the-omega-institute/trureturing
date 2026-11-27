# Relative derived subdivision and simplicial contiguity

## Abstract

Relative derived subdivision and simplicial contiguity

**Definition 1.1 (The relative derived complex).**

Lean statement: `D5/S3/Topology/RelativeDerivedContiguity.relativeDerived`

*Formalization.* `D5/S3/Topology/RelativeDerivedContiguity.relativeDerived` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Use the disjoint union of the old vertex labels and the faces of K outside A. A nonempty finite set of these labels is a face when its old labels, if nonempty, form a face of A, its outside faces form an inclusion chain, and every outside face contains all its old labels. Taking a nonempty subset preserves these three conditions.

**Theorem 1.2 (Contiguity after relative derived subdivision).**

Lean statement: `D5/S3/Topology/RelativeDerivedContiguity.relative_subdivision_preserves_contiguity`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/RelativeDerivedContiguity.relative_subdivision_preserves_contiguity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Let K and L be complexes on vertex types V and W, with V finite and W having decidable equality. Assume A is contained in K and every face of K or L whose vertices lie in A or B, respectively, belongs to that base. For each vertex of K, both vertex maps f and g preserve and reflect membership in the base, and the union of their images of each face of K is a face of L. Then a finite simplicial contiguity chain joins the induced maps on the relative derived complexes. Each induced map sends old labels by the original vertex map and outside faces to their images outside B. The proof uses the union of the two face images as a common exterior map, interpolates the exterior by face cardinality while holding the base map fixed, and changes the base map once at the common exterior map. The retained base is full, and each intermediate map sends base and exterior vertices to the corresponding parts of the target. Each adjacent step therefore satisfies the hypotheses for another relative subdivision.

## References

- Truth anchor: `D5/S3/Topology/RelativeDerivedContiguity.relativeDerived`
- Truth anchor: `D5/S3/Topology/RelativeDerivedContiguity.relative_subdivision_preserves_contiguity`
- Dependency: [D5/S3/Topology/DescendingClosureContiguity](DescendingClosureContiguity.md)
