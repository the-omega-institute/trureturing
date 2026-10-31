# Original Gaussian Determinant and Cutoff Limit

## Abstract

Original Gaussian Determinant and Cutoff Limit

The determinant uses the literal signed entries of OriginalGaussianMatrix and the complex square-summable operator and square cutoffs of OriginalGaussianResolvent. Coordinate n represents the positive frequency n+1. The cutoff is the actual finiteSection N z, including N=0.

The closed-cycle logarithm uses the actual signed entries at positive frequencies, with even walk length 2*(k+1) and divisor k+1. Absolute values are taken on each edge before summing internal vertices. At the negative real radius, the original signs cancel and realize these absolute walks by the same original operator. Its norm bound and a summable geometric coordinate majorant control all cycle lengths. The determinant gaussianDet is the exponential of this absolutely convergent cycle logarithm.

The finite logarithm uses traces of powers of the literal finiteSection N z. Exact zero extension identifies these powers with sectionOp powers, and dominated convergence first passes the spatial cutoff through the coordinate trace, then through the cycle-length series. For real z, one Hermitian spectral eigenbasis works simultaneously for all powers. The actual spectral norm bound and the scalar logarithm series give det(1-(finiteSection N z)^2)=exp(finiteLog N z), including N=0. Polynomial finite entries and a local summable series majorant prove finite-log holomorphy; the identity theorem extends this equality to every complex z with norm(z)<1. Consequently the literal finite determinants converge pointwise to gaussianDet. The square is taken after cutoff.

The infinite signed-cycle logarithm has a direct holomorphy argument on the open unit disk. Polynomial signed entries and a summable geometric bound control the internal-vertex sum by induction on walk length. A second geometric envelope controls the infinite diagonal trace at each positive even length, and the cycle-length majorant controls the logarithm series. Each bound is uniform on a smaller disk containing the evaluation point. Exponentiation then gives holomorphy of gaussianDet; this argument does not require uniform spatial cutoff convergence.

Uniform spatial cutoff convergence, identification with a period expression, and physical or string-theoretic realization are not asserted. The spectral and analytic ingredients are classical; these results are the source-specific composition for the original signed kernel.

**Definition 1.1 (gaussianLogDet).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.gaussianLogDet`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.gaussianLogDet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Minus the sum of the actual even closed-cycle traces divided by k+1. On norm(z)<1 the series converges absolutely.

**Definition 1.2 (gaussianDet).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.gaussianDet`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.gaussianDet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex exponential of gaussianLogDet. The cutoff theorem identifies it with the limit of the actual finite Gaussian determinants.

**Definition 1.3 (finiteLog).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.finiteLog`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.finiteLog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Minus the sum of tr((finiteSection N z)^(2*(k+1)))/(k+1). The powers use the matrix cut off before multiplication; the length-series majorant is independent of N.

**Theorem 1.4 (finite_determinant_identity).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.finite_determinant_identity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.finite_determinant_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural cutoff N and complex norm(z)<1, the determinant of 1-(finiteSection N z)^2 equals exp(finiteLog N z). This includes the empty determinant and arbitrary complex phases; Hermitian diagonalization is used only on the real slice.

**Theorem 1.5 (finite_determinants_tendsto).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.finite_determinants_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.finite_determinants_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every complex point of the open unit disk, det(1-(finiteSection N z)^2) tends to gaussianDet z as N tends to infinity. This is pointwise spatial cutoff convergence, with no period identity or physical realization premise.

**Theorem 1.6 (gaussianLogDet_differentiableOn).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.gaussianLogDet_differentiableOn`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.gaussianLogDet_differentiableOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complex differentiability of the actual infinite signed-cycle logarithm gaussianLogDet on the full open unit disk. Summable majorants on each smaller disk control the internal vertices, the outer diagonal vertex, and the cycle length.

**Theorem 1.7 (gaussianDet_differentiableOn).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.gaussianDet_differentiableOn`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.gaussianDet_differentiableOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complex differentiability of gaussianDet on the full open unit disk, by composition of the actual infinite signed-cycle logarithm with the complex exponential. No period identity or physical realization premise is used.

**Definition 1.8 (unit1Geo).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.unit1Geo`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.unit1Geo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two-coordinate geometric majorant used by compact-uniform operator cutoffs.

**Theorem 1.9 (unit1Geo_summable).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.unit1Geo_summable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.unit1Geo_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The geometric coordinate majorant is summable at every nonnegative radius below one.

**Theorem 1.10 (unit1Power_coordinate_bound).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.unit1Power_coordinate_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.unit1Power_coordinate_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each coordinate of an operator power applied to a unit basis vector is bounded by the corresponding power of the operator norm.

**Theorem 1.11 (unit1Section_power_coordinate).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.unit1Section_power_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.unit1Section_power_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each finite matrix-power coordinate agrees with the corresponding embedded section-operator power coordinate, including power zero.

**Theorem 1.12 (unit1Majorant_summable).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.unit1Majorant_summable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.unit1Majorant_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cycle-length majorant is summable on each smaller disk.

**Theorem 1.13 (finiteLogTerm_bound).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.finiteLogTerm_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.finiteLogTerm_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each literal finite logarithm term is bounded by the same cycle-length majorant independently of the section dimension.

**Theorem 1.14 (finiteLog_tendsto).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.finiteLog_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.finiteLog_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual finite logarithms converge pointwise to the infinite signed-cycle logarithm on the full unit disk.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.finiteLog`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.finiteLogTerm_bound`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.finiteLog_tendsto`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.finite_determinant_identity`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.finite_determinants_tendsto`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.gaussianDet`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.gaussianDet_differentiableOn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.gaussianLogDet`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.gaussianLogDet_differentiableOn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.unit1Geo`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.unit1Geo_summable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.unit1Majorant_summable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.unit1Power_coordinate_bound`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.unit1Section_power_coordinate`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent](OriginalGaussianResolvent.md)
