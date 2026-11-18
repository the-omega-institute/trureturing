# Finite Original Gaussian Positive Source Equations and T Germ

## Abstract

Finite Original Gaussian Positive Source Equations and T Germ

**Theorem 1.1 (positive_t_mode_equations).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFinitePositiveGerm.positive_t_mode_equations`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFinitePositiveGerm.positive_t_mode_equations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural p,q and real 0<r<1, the complete t=P-k*a(p)*a(q) satisfies L-R=(1-r)*(U(p)*V(q)-V(p)*U(q))/2 and 2*r*tPrime-L-R=(1-r)*(V(p)*V(q)-U(p)*U(q))/2. U and V are exactly the original signed source-frequency and source-jet expressions. L and R use negativeZeroT on their zero-index predecessors. The proof restores the actual Picard-Fuchs period term to P_euler_stencil and uses the genuine sqrt(1-r) source normalization. Symmetry supplies the second direction; no zero-boundary substitution is made.

**Theorem 1.2 (externalT_positive_finite_germ).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFinitePositiveGerm.externalT_positive_finite_germ`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFinitePositiveGerm.externalT_positive_finite_germ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each natural p,q, the literal full externalT(true,p,true,q,z) equals candidateT(p,q,z) for all complex z in some neighborhood of zero. The candidate is the actual finite P minus the actual logarithmic period term, composed with z squared. Literal differentiability supplies actual analytic scalar expansions. The concrete original and candidate equations have identical signed crossing boundaries; only after their subtraction do the guarded positive differences have zero predecessors. The existing coefficient nonresonance theorem then proves this unconditional germ equality. No common mode radius, disk-wide equality, negative sign sector, or J identification is claimed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFinitePositiveGerm.externalT_positive_finite_germ`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFinitePositiveGerm.positive_t_mode_equations`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianExternalGermCoefficientBridge](OriginalGaussianExternalGermCoefficientBridge.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteEulerStencil](OriginalGaussianFiniteEulerStencil.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource](../OriginalGaussianExternalGeneratedSource.md)
