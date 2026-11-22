# The original four-point diagonal germ

## Abstract

The original four-point diagonal germ in the negative square coordinate

**Definition 1.1 (Native sewn charge-sector sum).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm.chargeSectorSewn`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm.chargeSectorSewn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a fixed lattice datum, charge class, four occupations and complex sewing coordinate, sum the sewn charge terms in the class with zero contribution from all other charges.

**Theorem 1.2 (Analytic descent of each sewn charge coset).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm.cosetSeries_negative_square_germ`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm.cosetSeries_negative_square_germ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let D have positive definite real Gram matrix and unit Gram determinant. For a mod-two charge class a, let fₐ(w) be the original sewn charge sum for a after the finite lowering and Laurent projection in diagonalSewn. At each fixed occupation the charge terms use q on the left and −q on the right. The charge-normal bound gives a summable majorant on a closed disk of radius 0 < r < 1, and the projected sum is analytic at zero.

On the diagonal t = E + t₀, the left exponent and the right exponent −2t − 2 each shift by −2E from their values at E = 0. This cancels the energy shift in each selector, so one finite projection gives the coefficients at every E.

For any Taylor radius R > 0 chosen strictly inside a disk of expansion at zero, absolute summability of the Taylor coefficients at R yields absolute summability of the descended coefficients at R². Their degree-E coefficient is (−1)^E times the ordinary Taylor coefficient of fₐ of order 2E, equivalently the coefficient of degree E of cosetSeries at t = E + t₀ rescaled by −1. The descended germ Gₐ satisfies Gₐ(−w²) = (fₐ(w) + fₐ(−w))/2 near zero. The two sewing evaluations use w and −w and enter the average with plus signs.

**Theorem 1.3 (The actual fourM germ at all orders).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm.fourM_scalar_negative_square_germ`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm.fourM_scalar_negative_square_germ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume in addition that D has rank 24. The actual minus-one parity states u = P ⊗ x and v = Q ⊗ y have L₀-weights H and K. For every E in ℕ, the degree-E Taylor coefficient of a single holomorphic germ G is the actual fourMScalar at modes H + K − E − 1 and E + t₀ on u, v, R ⊗ z, S ⊗ d.

Near zero, G(−w²) is the sum over mod-two charge classes a of ((fₐ(w) + fₐ(−w))/2) · groundForm(D,y,Cₐx) · groundForm(D,d,Cₐz). Here Cₐ is the charge operator for the actual ground representation. The ordered left pairing is (y,Cₐx) and the ordered right pairing is (d,Cₐz). The finite coset sum gives the germ, and the actual energy-coefficient identity identifies its coefficients for all E.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm.chargeSectorSewn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm.cosetSeries_negative_square_germ`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm.fourM_scalar_negative_square_germ`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeNormal](OriginalFourMChargeNormal.md)
