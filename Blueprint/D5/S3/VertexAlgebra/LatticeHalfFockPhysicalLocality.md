# Two-Branch Locality

## Abstract

Physical coefficient locality of the actual normalized tensor fields

For an arbitrary even integral lattice D, hu:IsUnit(det G), native charges a,b, integers e,f and every unrestricted ActualTensor state, put g=B(a,b), N=abs(g), q_a=B(a,a) and c_a=2^(-q_a). The delivered chargedCoefficient has the cover prefactor x^(-q_a). With physical coordinates z=x^2 and w=y^2, multiplication by (z-w)^N uses the doubled cover shifts e-2(N-j) and f-2j. Both branch factors are retained for either sign of g.

**Theorem 1.1 (Locality on every actual tensor state).**

$$\operatorname{ChargedPhysicalLocality}\left(D, hu, a, b, e, f, state\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalLocality.charged_coefficient_physical_locality` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The finite sum over j=0,...,N of (-1)^j choose(N,j) times A_a[e-2(N-j)] A_b[f-2j] state minus the reverse composition vanishes. Both actual ordered products use the common native kernel and statewise finite supports. The two-branch PowerSeries identity produces a reciprocal polynomial; branch exchange identifies its two cleared kernels. The actual quotient ground representation supplies the central (-1)^g interchange sign, cancelling the reversed physical-difference sign. Pure-tensor readout and tensor induction prove the result without a locality premise or cutoffs.

Only the generic finite binomial identity is used from the ordinary difference library; ordinary cover delta is not a twisted Jacobi certificate. Coordinate monodromy is a separate native result. True all-state twisted Jacobi, physical iterates against ordinary Y, physical derivative covariance, corrected descendant normal products, reconstruction and orbifold intertwiners remain separate open obligations. Locality alone does not determine c_a. Classical FLM provenance, zero novelty claim; no full Leech, Vnatural, Monster, fusion, no-ghost, string or AdS realization follows.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalLocality.charged_coefficient_physical_locality`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel](LatticeHalfFockClearedKernel.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts](LatticeHalfFockOrderedProducts.md)
