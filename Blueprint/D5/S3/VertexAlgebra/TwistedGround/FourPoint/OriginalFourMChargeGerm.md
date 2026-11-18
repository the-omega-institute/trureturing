# The Original Four-Point Germ in the Negative Square

## Abstract

The negative-square coordinate of the original four-point Laurent diagonal.

**Definition 1.1 (Projected sewn charge sum).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm.diagonalSewn`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm.diagonalSewn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each external occupation, sum the native sewn terms over the chosen mod-two charge class. Apply the finite lowering powers, signed factorial weights and Laurent selectors to those sums. On the diagonal t = E + t₀, both Laurent exponents decrease by 2E and the selectors reduce to their degree-zero forms. The homogeneous right weights L and N give t₀ = L − N − 1.

**Theorem 1.2 (Negative-square descent for each charge class).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm.cosetSeries_negative_square_germ`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm.cosetSeries_negative_square_germ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normal convergence makes each fixed-occupation charge-class sum holomorphic near zero. The native Taylor formula uses the finite charge sublevel at total energy E. After finite lowering and projection, averaging the values at z and −z keeps order 2E and cancels the odd powers. In the variable −z² the degree-E coefficient is the original coset coefficient at t = E + t₀ multiplied by (−1)ᴱ.

**Theorem 1.3 (Taylor series of the original four-point scalar).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm.fourM_scalar_negative_square_germ`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm.fourM_scalar_negative_square_germ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the actual rank-24 parity and homogeneous left-state hypotheses, weight each descended coset by the ordered left and right ground forms and sum over charge classes. The resulting holomorphic germ has Taylor coefficients equal to the original four-point scalar at Laurent indices k = H + K − E − 1 and t = E + t₀ for every natural E. Its pullback near zero is the same ground-weighted sum of the actual sewn even parts.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm.cosetSeries_negative_square_germ`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm.diagonalSewn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm.fourM_scalar_negative_square_germ`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeNormal](../OriginalFourMChargeNormal.md)
