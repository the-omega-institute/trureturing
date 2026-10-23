# SourceCurrentIterate

## Abstract

Finite original source current iterate

**Theorem 1.1 (source_current_iterate_slice).**

Lean statement: `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceCurrentIterate.source_current_iterate_slice`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceCurrentIterate.source_current_iterate_slice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The source upper bound is at most the supplied cutoff K. All source states, signed physical lifts and signed current/residue modes remain arbitrary. The source state-field iterate has separate finite supports: the original source-field tail gives range((K-r).toNat), and the positive-current tail gives range(vectorFrequencyBound b+1). Mapping each source coefficient through the linear actual physical-slice map preserves both sums and the original epsilon sign. The resulting complete field equality is consumed by the native first-source current step.

## References

- Truth anchor: `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceCurrentIterate.source_current_iterate_slice`
- Dependency: [D5/S3/VertexAlgebra/GroundRightCurrentTransport/SectorPropagation](SectorPropagation.md)
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient](../NestedResidues/LatticeHalfFockSliceQuotient.md)
