# Actual Positive Gaussian J/T Kernel Unit

## Abstract

Actual Positive Gaussian J/T Kernel Unit

These results identify the literal original positive T modes on the full complex unit disk and the actual positive J generating kernel on the full original spatial bidisk. PositiveT.GeneratorIdentification supplies the actual positive T generating kernel on the same bidisk using its constructive absolute-convergence proof and this module's full-disk mode helper. The finite candidate and analytic candidate retain their existing definitions and original period and source normalization. The proofs preserve the existing analytic continuation and characteristic arguments; they introduce no germ, equality, summability or regularity premise.

**Theorem 1.1 (externalT_positive_finite_eq).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianPositiveIdentification.externalT_positive_finite_eq`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianPositiveIdentification.externalT_positive_finite_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural p,q and complex z with norm(z)<1, the actual externalT(true,p,true,q,z) equals the existing finite candidateT(p,q,z). The accepted concrete positive germ extends by the analytic identity principle on the preconnected unit disk. Literal differentiability supplies original analyticity, while candidateT_analyticOnNhd supplies candidate analyticity. No uniform mode germ radius is needed. This is a consumed bind-only helper, rather than new mathematical content: PositiveT.GeneratorIdentification.positiveT_eq_candidateT uses it on the live path from original modes to the constructive kernel sum.

**Theorem 1.2 (positiveJ_eq_candidateJ).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianPositiveIdentification.positiveJ_eq_candidateJ`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianPositiveIdentification.positiveJ_eq_candidateJ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real 0<r<1 and complex u,v with norm(u)+sqrt(r)<1 and norm(v)+sqrt(r)<1, the actual kernelMode(false,true,true,u,v,sqrt(r)) equals candidateJ(u,v,r). Both axes and the diagonal are included. Actual Banach-valued vector mode sums are holomorphic by local normal convergence; continuous bilinear resolvent factorization gives joint kernel differentiability. Subtracting the original and candidate spatial equations gives a homogeneous PDE. Along contracting rational characteristics, the squared weighted difference has zero derivative on the closed real unit interval and vanishes at zero. Its value at one is the square of the desired difference. There is no division by a spatial coordinate or assumed origin value.

The companion PositiveT.GeneratorIdentification proves rational positive T generator reconstruction with derived absolute convergence. Finite J mode extraction and all other sign sectors remain later steps. This positive Gaussian source unit does not complete VOA, CFT, string theory or AdS/CFT.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianPositiveIdentification.externalT_positive_finite_eq`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianPositiveIdentification.positiveJ_eq_candidateJ`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFinitePositiveGerm](OriginalGaussianFinitePositiveGerm.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate](../OriginalGaussianExternalAnalyticCandidate.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums](../OriginalGaussianExternalRadialSums.md)
