# The first-subdivision relative covering number of a simplex horn

## Abstract

The first-subdivision relative covering number of a simplex horn

**Theorem 1.1 (A simplex horn needs exactly one relative piece per facet at the first subdivision).**

Lean statement: `D5/S3/Topology/StableCategory/RelativeHornCover.isLeast_horn_relative_lower_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/RelativeHornCover.isLeast_horn_relative_lower_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Adjoin a greatest element to the nonempty face poset of a horn in a simplex of dimension at least two. After one chain subdivision, cover by lower sets that contain the entire old region and admit order homotopies into it fixing it pointwise. Cyclic maximal chains in the horn are pairwise disjoint, and the predecessor criterion allows only one of these chains through the new maximum per relative piece. A chart for every horn facet attains the lower bound.

## References

- Truth anchor: `D5/S3/Topology/StableCategory/RelativeHornCover.isLeast_horn_relative_lower_cover`
- Dependency: [D5/S3/Topology/StableCategory/RelativeCoverNecessity](RelativeCoverNecessity.md)
