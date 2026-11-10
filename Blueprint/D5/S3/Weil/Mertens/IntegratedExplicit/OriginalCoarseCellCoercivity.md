# Finite-cell coercivity for the original positive kernel

## Abstract

Finite-cell coercivity for the original positive kernel

**Theorem 1.1 (An arbitrary positive coercivity constant).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalCoarseCellCoercivity.original_coarse_cell_coercivity`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalCoarseCellCoercivity.original_coarse_cell_coercivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive window length D and positive beta, one finite strict uniform grid from zero to D works for every finite complex atomic family in the closed window with zero total mass. If the literal complex integral of the inclusive prefix vanishes on every coarse cell, beta times its whole-line squared L2 mass is at most the real part of the original quadratic form for P. Empty families, repeated locations, endpoint locations and zero energy are included.

The full original P is exp(-abs(t)/2) times trivialT(abs(t)). ActualKernelMomentCertificate.pMultiplier uses every trivialCoeff(n) and actual rate 2*(n+1)+1/2; complete_positive_mixture_spectral_identity supplies the exact full-mixture energy. OriginalActualFourier.Ahat has kernel exp(-i*xi*u), and rho has density norm(Ahat)^2/(2*pi). The angular Plancherel theorem gives total rho mass equal to the actual prefix energy.

For a uniform cell width h and radius R, cell cancellation bounds the rho mass of [-R,R] by D*R^3*h^2/pi times the prefix energy. Subtracting the phase at each left endpoint, applying the phase Lipschitz bound and summing the cell integrals gives this estimate. A sufficiently fine finite grid makes this band contain at most half the spatial energy. The actual positive-mixture nonnegativity controls the band, while the logarithmic multiplier lower bound controls its complement. The radius and grid are selected before the atom type and coefficients; the argument never divides by their energy.

The conclusion concerns finite atomic prefixes and literal cell integrals. Hat-function readouts, completed detail spaces and operator realizations require additional constructions.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalCoarseCellCoercivity.original_coarse_cell_coercivity`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentMixture](ActualKernelMomentMixture.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/LineFourier](../../ZetaGamma/FormCore/LineFourier.md)
