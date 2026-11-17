# Literal sewn source analytic cutoff passage

## Abstract

OriginalGaussianSewnAnalytic

The finite function is exp(-(rank/2)*finiteLog) times exp(effectiveConstant) times the ordinary affine coefficient of the actual effective kernel and mean. The limiting function uses gaussianLogDet, explicitEffectiveKernel, the literal left and right sourceExternal means, and the full chargeNorm*sourceConstant. The source constant retains its inverse frequency denominator. The ordinary coefficient of order m is iteratedDeriv m at zero divided by m factorial.

Normalized finite sections have norm below one throughout the unit disk. Their squared resolvent is holomorphic. The proved ordered inverse similarities express the raw inverses through this resolvent without requiring raw contraction on that disk. Finite matrix expressions and the finite polynomial formula for the affine coefficient give finite sewn holomorphy. The original finite logarithm holomorphy supplier is used directly.

The accepted uniform kernel, mean, constant and logarithm limits combine in a finite tuple. On a compact subdisk, uniform convergence bounds the eventual finite tuples inside a common compact ball. The continuous exponential and affine coefficient map is uniformly continuous on that ball, so composition gives uniform convergence of the actual sewn functions. Locally uniform derivative convergence can then be iterated to every fixed order. This does not exchange an occupation series with external coefficients and does not identify the result with the original fixed-energy source sum.

**Definition 1.1 (Literal limiting source means).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.explicitMean`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.explicitMean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The left sign is -1+sourceExternal and the right sign is 1-sourceExternal.

**Definition 1.2 (Actual finite sewn function).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.finiteSewn`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.finiteSewn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cutoff is the original finite effective data and finite trace logarithm.

**Definition 1.3 (Literal explicit limiting function).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.sewn`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.sewn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The limiting constant is the full chargeNorm*sourceConstant, with no residual overall half.

**Definition 1.4 (Ordinary scalar Taylor coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.coefficient`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.coefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient uses the complete factorial of its derivative order.

**Theorem 1.5 (Finite sewn holomorphy).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.finiteSewn_differentiableOn`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.finiteSewn_differentiableOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite sewn function is holomorphic on the same open unit disk.

**Theorem 1.6 (Uniform passage through the finite coefficient polynomial).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.finiteSewn_tendstoUniformlyOn`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.finiteSewn_tendstoUniformlyOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual sewn functions converge uniformly on every nonnegative closed subdisk of radius less than one.

**Theorem 1.7 (Locally uniform literal cutoff limit).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.finiteSewn_tendstoLocallyUniformlyOn`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.finiteSewn_tendstoLocallyUniformlyOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Closed subdisks provide the neighbourhoods required for locally uniform convergence.

**Theorem 1.8 (Holomorphy of the literal limit).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.sewn_differentiableOn`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.sewn_differentiableOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The locally uniform limit of the proved finite holomorphic functions is holomorphic.

**Theorem 1.9 (Every fixed ordinary coefficient passes to the limit).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.finiteSewn_coefficient_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.finiteSewn_coefficient_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Iterate the upstream locally uniform derivative theorem, evaluate at zero, and divide by the complete factorial. Order zero is included. Application at order 2*n gives the analytic cutoff passage, while the original source identification remains a separate obligation.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.explicitMean`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.finiteSewn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.finiteSewn_coefficient_tendsto`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.finiteSewn_differentiableOn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.finiteSewn_tendstoLocallyUniformlyOn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.finiteSewn_tendstoUniformlyOn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.sewn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.sewn_differentiableOn`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientContinuity](GaussianCoefficientContinuity.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm](OriginalGaussianSourceGerm.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformDeterminant](OriginalGaussianUniformDeterminant.md)
