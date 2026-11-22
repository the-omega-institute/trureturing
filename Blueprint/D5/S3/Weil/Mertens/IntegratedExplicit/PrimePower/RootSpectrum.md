# The signed transform and its primitive

## Abstract

The actual zero spectrum at a real root cutoff

**Definition 1.1 (The log density at degree r).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootSpectrum.rootDensity`

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootSpectrum.rootDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For r > 1, each actual nontrivial zero occurrence rho contributes the coefficient -r/[rho(r-rho)] times exp((rho/r-1/2)u). Take the real part after summation.

**Theorem 1.2 (The weighted transform of the zero tail).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootSpectrum.root_spectral_transform`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootSpectrum.root_spectral_transform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At y = exp(v), the substitution s = exp(w) changes the spectral exponent from rho-1 to rho-r. The open critical strip and absolute coefficient summability give an integrable majorant on w > v. Termwise integration supplies 1/(r-rho). Combining the integrated and boundary terms gives the density at u = rv.

**Definition 1.3 (The endpoint primitive).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootSpectrum.rootPrimitive`

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootSpectrum.rootPrimitive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For x > 0 the primitive is the real part of the sum of 2r² x^(rho/r-1/2)/[rho(r-rho)(r-2rho)] over the same occurrences.

**Theorem 1.4 (The oriented integral between two log cutoffs).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootSpectrum.root_density_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootSpectrum.root_density_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The density is interval integrable for every pair of real log cutoffs. Absolute convergence on each bounded interval permits termwise integration, and the result is the primitive at exp(b) minus the primitive at exp(a). The identity includes reversed and equal endpoints.

**Theorem 1.5 (The unconditional error after subtracting the spectrum).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootSpectrum.root_centered_error`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootSpectrum.root_centered_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r > 1 and v at least log(2), set x = exp(rv). The centered normalized Chebyshev tail at degree r differs from the log density at rv by at most (2r-1)|log(2π)|x^(-1/2). The pointwise residual in the complete formula and its weighted integral supply the two terms in the bound.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootSpectrum.rootDensity`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootSpectrum.rootPrimitive`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootSpectrum.root_centered_error`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootSpectrum.root_density_integral`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootSpectrum.root_spectral_transform`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHRootCorrection](RHRootCorrection.md)
