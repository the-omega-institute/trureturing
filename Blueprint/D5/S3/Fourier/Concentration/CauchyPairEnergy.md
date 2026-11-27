# Cauchy energy and a Lorentz pair sum

## Abstract

Localization of the Cauchy-smoothed energy gives a finite Lorentz pair-sum lower bound.

**Theorem 1.1 (Mass in an enlarged interval).**

Lean statement: `D5/S3/Fourier/Concentration/CauchyPairEnergy.cauchy_mass_buffer_interval`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/CauchyPairEnergy.cauchy_mass_buffer_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When -R <= Y+R, the mass in [-R,Y+R] of the unit-scale Cauchy density centered at x is (arctan(Y+R-x) + arctan(R+x))/pi. For x in [0,Y] and R > 0 this is at least 2 arctan(R)/pi.

**Theorem 1.2 (Energy controls the magnitude of the total coefficient).**

Lean statement: `D5/S3/Fourier/Concentration/CauchyPairEnergy.lorentz_pair_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/CauchyPairEnergy.lorentz_pair_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a finite family of locations x_j in [0,Y], complex coefficients a_j, and any real R. Write S = sum a_j and N = sum |a_j|. The ordered-pair sum of Re(a_i conjugate(a_j)) times 4/(4+(x_i-x_j)^2) is nonnegative for R <= 0 or an empty family. For R > 0 and a nonempty family it is at least 2 pi/(Y+2R) times the square of max(|S|-(1-2 arctan(R)/pi) N,0).

The sum equals 2 pi times the squared L2 norm of the combination of translated unit-scale Cauchy densities. The probability convolution identity gives the kernel of scale two. For R > 0, on [-R,Y+R], the integral of the smoothed combination differs from S by at most (1-2 arctan(R)/pi) N. Cauchy-Schwarz converts this magnitude bound into the energy bound. For R <= 0, the triangle inequality makes the lower bound zero.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/CauchyPairEnergy.cauchy_mass_buffer_interval`
- Truth anchor: `D5/S3/Fourier/Concentration/CauchyPairEnergy.lorentz_pair_lower_bound`
- Dependency: [D5/S3/Analytic/ShiftedXiPoisson/ShiftedPoissonSemigroup](../../Analytic/ShiftedXiPoisson/ShiftedPoissonSemigroup.md)
