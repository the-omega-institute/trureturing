# Original Gaussian Cubic Finite Principal Parts

## Abstract

Original Gaussian Cubic Finite Principal Parts

Finite binomial numerators determine the principal parts of the original current. The literal TT and UT kernels have degree-dependent pole bounds at all indices, with the original square-root equation retained for external roots.

These sources are an implementation checkpoint. Native verification and independent admission review are separate requirements; no official acceptance or physical realization is asserted. Full four-halfmode geometry, two-source transport, identityK crossing, Monster moonshine, VOA/CFT/anomaly/fusion, complete string theory and AdS/CFT remain unfinished.

**Theorem 1.1 (finite_current_numerator_degree).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.finite_current_numerator_degree`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.finite_current_numerator_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual truncation polynomial for the current has degree strictly below s+1; this degree supplier is consumed by finite numerator uniqueness.

**Theorem 1.2 (finite_current_negative_coeff).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.finite_current_negative_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.finite_current_negative_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every negative Laurent exponent, the current has exactly the prescribed principal coefficient, including the totalized s=0 case.

**Theorem 1.3 (finite_current_residue).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.finite_current_residue`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.finite_current_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual finite current Laurent series has zero residue at exponent minus one for every natural index.

**Theorem 1.4 (finite_current_regular_coeff).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.finite_current_regular_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.finite_current_regular_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive regular index, the entire finite-current tail equals the original pairScalar, including equal input and output indices.

**Theorem 1.5 (currentRow_eq_finite_numerator).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.currentRow_eq_finite_numerator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.currentRow_eq_finite_numerator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluation of the explicit finite numerator gives the unchanged original currentRow, with arbitrary complex external scalar and totalized b=0.

**Theorem 1.6 (finite_current_numerator_unique).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.finite_current_numerator_unique`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.finite_current_numerator_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An arbitrary polynomial of the stated strict degree is forced to the constructed numerator by its truncated half-series product.

**Theorem 1.7 (external_root_exclusions).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.external_root_exclusions`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.external_root_exclusions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original root equation alone forces a nonzero root and excludes b=-1; no square-root convention is selected.

**Theorem 1.8 (literal_polar_derivative_identity).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.literal_polar_derivative_identity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.literal_polar_derivative_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expand the literal cubic derivative numerator and identify it with the independently defined polar polynomial.

**Theorem 1.9 (literal_diagonal_polynomials).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.literal_diagonal_polynomials`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.literal_diagonal_polynomials` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expand the literal polar and cubic at a=b+v, retaining the full polynomial coefficients without a finite testing cutoff.

**Theorem 1.10 (literal_pullback_polar).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.literal_pullback_polar`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.literal_pullback_polar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After multiplication by u squared, the literal rational substitution a=x/u gives the original pulled-back polar when u is nonzero.

**Theorem 1.11 (cubic_tt_pole_bound).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.cubic_tt_pole_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.cubic_tt_pole_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every permitted modulus degree and negative mode, the actual TT coefficient vanishes under the original bound d<=s.

**Theorem 1.12 (cubic_ut_pole_bound).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.cubic_ut_pole_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.cubic_ut_pole_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every permitted modulus degree and negative mode, the actual UT coefficient vanishes under the original strict bound d<s.

**Theorem 1.13 (cubic_ut_degree_zero).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.cubic_ut_degree_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.cubic_ut_degree_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compute the actual degree-zero UT power-series coefficient directly from the original kernel and scalar constant term.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.cubic_tt_pole_bound`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.cubic_ut_degree_zero`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.cubic_ut_pole_bound`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.currentRow_eq_finite_numerator`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.external_root_exclusions`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.finite_current_negative_coeff`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.finite_current_numerator_degree`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.finite_current_numerator_unique`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.finite_current_regular_coeff`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.finite_current_residue`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.literal_diagonal_polynomials`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.literal_polar_derivative_identity`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.literal_pullback_polar`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection](../LatticeHalfFockFiniteCorrection.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicKernel](OriginalGaussianCubicKernel.md)
