# Mode sums and the elliptic half-coordinate

## Abstract

Native signed Gaussian covariance and source

The flags l and k label the native legs, with false on the left and true on the right. The independent flags e and f label the signed external modes, with true denoting the positive label. Write P for the Euler slit period and C(r) for its period correction. The radial variable w gives r = w².

**Definition 1.1 (Tagging an external mode by its leg).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.taggedMode`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.taggedMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any label type X, taggedMode places x in the left summand of X ⊕ X when right is false and in the right summand when right is true.

**Definition 1.2 (Signed covariance generator).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.covarianceMode`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.covarianceMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At complex u, v and r, equal legs use candidateJ(e,f,u,v,r) plus the Cauchy free term when e ≠ f. Unequal legs use −candidateT(e,f,u,v,r) in either order.

**Theorem 1.3 (Bivariate sum of the actual covariance entries).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_covariance_hasSum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_covariance_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any lattice data D, colors i and j and flags l, k, e and f, assume ‖u‖ + ‖w‖ < 1 and ‖v‖ + ‖w‖ < 1. The sum over natural modes p and q of the actual effective kernel entry with tagged labels (e,i,p) and (f,j,q), weighted by u^p v^q, is gramComplex(D,i,j) times covarianceMode(l,k,e,f,u,v,w²).

**Theorem 1.4 (Native Taylor extraction).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_tagged_entry`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_tagged_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If ‖w‖ < 1, any two tagged labels recover their actual effective kernel entry by taking the u coefficient at the first mode index and then the v coefficient at the second mode index of the Gram-weighted covariance generator at r = w². The label type is arbitrary and repeated labels and both crossed leg orders are allowed.

**Theorem 1.5 (Actual mean in a fixed signed mode).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_mean`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_mean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any lattice charge a and finite external label type with decidable equality, take a label of sign e, color i and mode p at ‖w‖ < 1. Its actual mean is the bilinear pairing of the unit color charge with a times sourceAmplitude(e,p,w²)/period(w²), multiplied by −1 on the left leg and +1 on the right.

**Theorem 1.6 (Native covariance as a corrected spatial kernel).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_spatial_overlap`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_spatial_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On ‖u‖ + ‖w‖ < 1 and ‖v‖ + ‖w‖ < 1 with u, v and G(e,f,u,v) nonzero, set r = w² and m = sourceMode(e,u,r) sourceMode(f,v,r). On either equal leg, the generator is m times spatialKernel at parameter 1−r and coordinates rightChart(e,u), rightChart(f,v), with C(r) subtracted inside that product and the Cauchy term subtracted only for e = f. For either unequal-leg order it is −m times the corrected kernel at rightChart(e,u), leftChart(f,r,v).

**Theorem 1.7 (Finite native diagonal).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either leg l and sign e, with ‖u‖ + ‖w‖ < 1, covarianceMode(l,l,e,e,·,·,r) tends at (u,u) to (r/4−C(r))/(b(u)h(e,u,r)) + r²u/(8(b(u)h(e,u,r))²), where r = w². The ordinary neighborhood limit includes u = 0.

**Definition 1.8 (Orientation sign of a native leg).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.legSign`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.legSign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex source orientation is +1 on the left leg and −1 on the right.

**Definition 1.9 (Oriented half-coordinate source).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.signedHalfSource`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.signedHalfSource` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For leg right and mode sign e, the oriented source at complex u and r is legSign(right) times sourceMode(e,u,r).

**Theorem 1.10 (Sum of the actual mode means).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_mean_hasSum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_mean_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any lattice data D, charge a, color i and flags l and e, assume ‖u‖ + ‖w‖ < 1. Summing the actual tagged means of the singleton labels (e,i,p) against uᵖ gives the negative bilinear pairing of the unit color charge with a times signedHalfSource(l,e,u,w²)/P(w²).

**Theorem 1.11 (Pullback of the elliptic differential).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.half_coordinate_pullback`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.half_coordinate_pullback` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either leg and either sign, take nonzero complex q and r with ‖q²‖ + ‖r‖ < 1. The native lift (x(q),y(q)) satisfies y² = x(x−1)(x−(1−r)) and y ≠ 0. Its x derivative at q is 2y times signedHalfSource(right,e,q²,r), so the source is the coefficient of the pullback of dx/(2y).

**Theorem 1.12 (Restored covariance on the native elliptic chart).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_geometric_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_geometric_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any l, k, e and f, set u = q², v = Q² and r = w². Assume ‖u‖ + ‖w‖ < 1 and ‖v‖ + ‖w‖ < 1, with q, Q, w and G(e,f,u,v) nonzero. Write x₀ = rightChart(e,u), X₀ = rightChart(f,v) and X₁ = leftChart(f,r,v). Require x₀−1, X₀−1, x₀−X₀ and x₀−X₁ to be nonzero.

Adding the Cauchy term only when l = k and e = f gives the corrected spatial kernel at the two actual native lift coordinates and parameter 1−r, multiplied by the two oriented sources signedHalfSource(l,e,u,r) and signedHalfSource(k,f,v,r).

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.covarianceMode`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.half_coordinate_pullback`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.legSign`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_covariance_hasSum`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_diagonal`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_geometric_covariance`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_mean`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_mean_hasSum`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_spatial_overlap`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_tagged_entry`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.signedHalfSource`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.taggedMode`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications](../ComplexRadial/Applications.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMActualChart](OriginalFourMActualChart.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource](OriginalFourMPeriodSource.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic](../OriginalGaussianSewnAnalytic.md)
