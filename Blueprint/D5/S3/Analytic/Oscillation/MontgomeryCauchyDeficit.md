# A positive phase deficit from a Cauchy energy bound

## Abstract

An upper Montgomery pair-sum bound strictly below the Cauchy threshold yields a fractional phase deficit.

**Theorem 1.1 (Phase deficit on fixed logarithmic bands).**

Lean statement: `D5/S3/Analytic/Oscillation/MontgomeryCauchyDeficit.fractional_deficit_of_cauchy_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/MontgomeryCauchyDeficit.fractional_deficit_of_cauchy_cap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a locally finite positive spectrum with the inclusive counting asymptotic N(Y) divided by Y log Y tending to c = 1/(2 pi). Assume the unnormalized Montgomery pair sum is bounded above by kappa Y (log Y)^2 for one fixed kappa < 2 pi c^2. For each fixed A > 1 the bound holds for all sufficiently large Y and uniformly at log Y <= |t| <= A log Y.

There is a fixed d > 0 such that on every such band, for sufficiently large Y, the magnitude of the multiplicity-weighted phase sum over ordinates through Y is at most (1-d)N(Y). Use the Cauchy lower estimate with R = epsilon Y. Choose epsilon small enough that the enlarged interval preserves the strict gap in the energy coefficient. The lost mass fraction tends to zero and the count asymptotic makes the gap uniform on each band.

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/MontgomeryCauchyDeficit.fractional_deficit_of_cauchy_cap`
- Dependency: [D5/S3/Analytic/Asymptotics/DirichletPolynomialMeanSquare](../Asymptotics/DirichletPolynomialMeanSquare.md)
- Dependency: [D5/S3/Analytic/Oscillation/MontgomeryWindow](MontgomeryWindow.md)
- Dependency: [D5/S3/Fourier/Concentration/CauchyPairEnergy](../../Fourier/Concentration/CauchyPairEnergy.md)
