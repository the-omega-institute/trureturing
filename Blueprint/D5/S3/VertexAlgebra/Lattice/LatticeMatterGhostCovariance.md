# The exact matter anomaly after shifted finite cancellation

## Abstract

The exact matter anomaly after shifted finite cancellation

Assume only that H is a two-sided inverse of the complex lattice Gram matrix. The original matter Virasoro theorem and original ghost weight-minus-one Ward identity determine the two commutators. The construction remains on the algebraic tensor product and uses no completion or tensor commutant assumption.

**Definition 1.1 (The shifted original-operator action family).**

Lean statement: `D5/S3/VertexAlgebra/LatticeMatterGhostCovariance.paired`

*Formalization.* `D5/S3/VertexAlgebra/LatticeMatterGhostCovariance.paired` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D,H and integers r,k, paired D H r k is the tensor map sugawaraMode D H k tensor BcGhostFock.c (r-k). Its statewise support is finite. Translating the finite captures by m maps to m+r supplies the actual noncentral cancellation.

**Theorem 1.2 (Original-operator covariance with the rank anomaly).**

Lean statement: `D5/S3/VertexAlgebra/LatticeMatterGhostCovariance.covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeMatterGhostCovariance.covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,H with H G=G H=1 and every integer r, [T,M_r+G_r]=-(rank(D)/12)(r^3-r) C_r. For a simple tensor choose U=U(v), V=U(sugawaraMode r v), d=max(0,-r), J=[r-A,U] and I=[min(-A-d,-r),max(V,U+d)]. I captures x, M_r x and G_r x, contains J and J-r, and contains the central index -r. A finite bijection m maps to m+r converts the matter noncentral coefficient into k-2r; it cancels the ghost coefficient 2r-k. At m=-r the central cubic is the negative of r^3-r. The statement neither constructs the total BRST charge nor proves nilpotence. The cubic ghost supplier, its composition with this matter term and later physical interpretation remain separate obligations.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeMatterGhostCovariance.covariance`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeMatterGhostCovariance.paired`
- Dependency: [D5/S3/VertexAlgebra/LatticeMatterGhostCoupling](LatticeMatterGhostCoupling.md)
