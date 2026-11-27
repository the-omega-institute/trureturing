# Summation of finite positive T modes

## Abstract

Identification of the original positive T generator

**Theorem 1.1 (Sum of the finite candidate modes).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/PositiveT/GeneratorIdentification.positiveT_hasSum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/PositiveT/GeneratorIdentification.positiveT_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real 0 < r < 1 and complex u and v with ‖u‖ + √r < 1 and ‖v‖ + √r < 1, the family t(p,q,(r : ℂ)) u^p v^q indexed by ℕ × ℕ has sum OriginalGaussianExternalAnalyticCandidate.candidateT(u,v,(r : ℂ)). Here t is the complete coefficient from OriginalGaussianFiniteCandidateModes, including the logarithmic period correction.

The binomial estimates bound the two denominator families by a polynomial in the indices times (1 + √r)^(p+q). With the source weights, the two geometric ratios ‖u‖(1 + √r) and ‖v‖(1 + √r) are less than one. Summing the inverse stencils gives E(u,v,r) times the first sum equal to one and E(u,v,r) times the second sum equal to the first. This proves E ≠ 0 and identifies the sums as 1/E and 1/E². The rectangular Cauchy product with the two positive source generators and subtraction of the period term give the stated candidate.

**Theorem 1.2 (Equality for the literal positive T kernel).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/PositiveT/GeneratorIdentification.positiveT_eq_candidateT`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/PositiveT/GeneratorIdentification.positiveT_eq_candidateT` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real 0 < r < 1 and complex u and v with ‖u‖ + √r < 1 and ‖v‖ + √r < 1, the original kernelMode(true,true,true,u,v,(√r : ℂ)) equals OriginalGaussianExternalAnalyticCandidate.candidateT(u,v,(r : ℂ)). The three true flags select the square resolvent and both positive source labels.

For each p and q, OriginalGaussianFinitePositiveGerm.externalT_positive_finite_germ gives equality between the literal positive externalT mode and the finite candidate near zero. Analyticity of both functions gives equality on the complex unit disk by AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq. At z = (√r : ℂ), z² = (r : ℂ), so this mode equality identifies every term of the literal kernel sum with the corresponding term of positiveT_hasSum, which evaluates the sum.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/PositiveT/GeneratorIdentification.positiveT_eq_candidateT`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/PositiveT/GeneratorIdentification.positiveT_hasSum`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFinitePositiveGerm](../FiniteMode/OriginalGaussianFinitePositiveGerm.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate](../OriginalGaussianExternalAnalyticCandidate.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums](../OriginalGaussianExternalRadialSums.md)
