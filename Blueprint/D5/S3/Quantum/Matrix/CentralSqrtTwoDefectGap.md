# Central square-root-two defect gap

## Abstract

Rank-one sector separation for the central square-root-two defect Jacobi family.

**Theorem 1.1 (Inverse gap from endpoint control).**

Lean statement: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.rank_one_gap_from_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.rank_one_gap_from_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real c,K,lambda,mu,x,y,z with c>0, K>0, (lambda-mu)z=cxy, 1<=K*x^2, 1<=K*y^2, and |z|<=1, one has c/K<=|lambda-mu|. This is the quantitative inverse-cubic bridge once K is the endpoint control constant.

**Theorem 1.2 (Rank-one cross-sector identity).**

Lean statement: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.rank_one_cross_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.rank_one_cross_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If A is real symmetric, B=A+c vv^T with v the coordinate vector at q, and Au=lambda u, Bv=mu v, then (mu-lambda)<u,v> =c*u(q)*v(q). The identity is proved by the matrix update and symmetry.

**Theorem 1.3 (Rank-one cross-sector gap).**

Lean statement: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.rank_one_gap_of_matrices`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.rank_one_gap_of_matrices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combining the preceding identity with endpoint controls 1<=K*u(q)^2 and 1<=K*v(q)^2 and |<u,v>|<=1 gives c/K<=|lambda-mu| for actual eigenpairs of the two symmetric matrices.

**Definition 1.4 (Central square-root-two edge sequence).**

Lean statement: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.centralEdges`

*Formalization.* `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.centralEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n>=1, centralEdges(n) is the edge sequence on Fin(2*n-1+1) whose unique central entry at n-1 is sqrt(2), with every other entry 1; the displayed dimension is 2*n under the stated threshold.

**Definition 1.5 (Actual central defect Jacobi matrix).**

Lean statement: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.centralDefect`

*Formalization.* `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.centralDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

centralDefect(n) is the zero-diagonal Jacobi matrix of dimension 2*n-1+1 with nearest-neighbour entries centralEdges(n), hence exactly the fixed central-sqrt(2) defect matrix from the source event after the threshold identification.

**Theorem 1.6 (Nonzero edge coefficients).**

Lean statement: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.centralEdges_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.centralEdges_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every entry of centralEdges(n) is nonzero for n>=1.

**Theorem 1.7 (Simple spectrum of the actual defect matrix).**

Lean statement: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.centralDefect_simple`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.centralDefect_simple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n>=1, centralDefect(n) has simple algebraic spectrum. This is the direct application of the existing endpoint-uniqueness Jacobi theorem and retains the complete matrix dimension.

The quantitative endpoint estimate, source quantization and adjacent-sector alternation needed for the complete uniform inverse-cubic event remain separate obligations. This module records the compiled rank-one bridge and the actual fixed matrix family.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.centralDefect`
- Truth anchor: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.centralDefect_simple`
- Truth anchor: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.centralEdges`
- Truth anchor: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.centralEdges_ne_zero`
- Truth anchor: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.rank_one_cross_identity`
- Truth anchor: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.rank_one_gap_from_identity`
- Truth anchor: `D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.rank_one_gap_of_matrices`
- Dependency: [D5/S3/Quantum/Matrix/GibbsStochasticSimpleSpectrum](GibbsStochasticSimpleSpectrum.md)
