# The square-cutoff primitive at common endpoints

## Abstract

Signed square-cutoff zero series

**Definition 1.1 (The complete log-coordinate zero tail).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.zeroTail`

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.zeroTail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each natural-number index is one actual nontrivial zero occurrence, with analytic multiplicity.

**Theorem 1.2 (Absolute control under RH).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.norm_zeroTail_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.norm_zeroTail_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum of the absolute coefficients is firstLiMass. Each log-coordinate exponential has norm exp(-u/2) under RH.

**Theorem 1.3 (The normalization of the existing zero series).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.zeroTail_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.zeroTail_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by exp(-u) converts the exponent rho to rho-1 for each occurrence.

**Definition 1.4 (Square-cutoff log density).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.squareDensity`

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.squareDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient is -2/[rho(2-rho)] at every occurrence and the exponential is exp((rho-1)u/2).

**Theorem 1.5 (The signed transform at the square cutoff).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.square_spectral_transform`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.square_spectral_transform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the weighted integral, the substitution s=exp(v) changes the mode exponent from rho-1 to rho-2. The norms of the weighted modes sum to an integrable multiple of exp(-3v/2) above the cutoff. The integrated mode introduces 1/(2-rho). Subtraction from the boundary mode and multiplication by -2 give the stated density coefficient.

**Definition 1.6 (The square-cutoff primitive).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.squarePrimitive`

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.squarePrimitive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The primitive holds the complex power x^((rho-1)/2) and coefficient 4/[rho(1-rho)(2-rho)] before taking real parts.

**Theorem 1.7 (The same occurrence at the half and full log phase).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.square_power_half_phase`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.square_power_half_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x>0 the power factors into x^(-1/4) times the actual phase at log(x)/2. Squaring that phase gives the actual phase at log(x).

**Theorem 1.8 (The square density integrates to an endpoint difference).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.square_density_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.square_density_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Absolute convergence on every finite interval permits termwise integration. Dividing by (rho-1)/2 produces the primitive coefficient, and the two values use the same occurrence indexing at their respective endpoints.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.norm_zeroTail_le`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.squareDensity`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.squarePrimitive`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.square_density_integral`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.square_power_half_phase`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.square_spectral_transform`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.zeroTail`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum.zeroTail_eq`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePhaseCluster](../PrimePhaseCluster.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope](../RHSharpActualEnvelope.md)
