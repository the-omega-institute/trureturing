# Gaussian spectral sums

## Abstract

Gaussian mass and continuous cosine sums of positive ordinates.

**Theorem 1.1 (Logarithmic counting growth).**

Lean statement: `D5/S3/Analytic/Oscillation/GaussianSpectrum.count_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/GaussianSpectrum.count_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the multiplicity-weighted count divided by T log T tends to 1/(2 pi), there is C>0 such that N(T) is at most C T log(2+T) for every T at least one. Monotonicity controls bounded cutoffs, and the limit controls the remaining cutoffs.

**Theorem 1.2 (Summability of inverse squares).**

Lean statement: `D5/S3/Analytic/Oscillation/GaussianSpectrum.inverse_square_summable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/GaussianSpectrum.inverse_square_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a locally finite positive spectrum with the counting asymptotic, the sum of multiplicity divided by the square of each ordinate converges. The finite cutoff at four and the convergent inverse-square tail cover the entire spectrum.

**Theorem 1.3 (Summable Gaussian coefficients).**

Lean statement: `D5/S3/Analytic/Oscillation/GaussianSpectrum.gaussian_coefficients_summable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/GaussianSpectrum.gaussian_coefficients_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every positive scale M, the multiplicity-weighted Gaussian coefficients are summable. The inequality exp(-x) <= 1/x for x>0 bounds each coefficient by 2 M squared times the multiplicity divided by the ordinate squared.

**Theorem 1.4 (Absolute convergence of the cosine series).**

Lean statement: `D5/S3/Analytic/Oscillation/GaussianSpectrum.gaussianCos_summable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/GaussianSpectrum.gaussianCos_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive M and real y, the Gaussian-weighted cosine series converges absolutely. The absolute value of each cosine is at most one, so the Gaussian coefficients form a summable majorant.

**Theorem 1.5 (Continuity of the cosine sum).**

Lean statement: `D5/S3/Analytic/Oscillation/GaussianSpectrum.gaussianCos_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/GaussianSpectrum.gaussianCos_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each positive M, the Gaussian spectral cosine sum is a continuous function of y. Each summand is continuous and its absolute value has a summable bound independent of y.

**Theorem 1.6 (Uniform bound by Gaussian mass).**

Lean statement: `D5/S3/Analytic/Oscillation/GaussianSpectrum.abs_gaussianCos_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/GaussianSpectrum.abs_gaussianCos_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive M and every real y, the absolute value of the Gaussian cosine sum is at most the total Gaussian mass at scale M.

**Theorem 1.7 (Gaussian spectral mass).**

Lean statement: `D5/S3/Analytic/Oscillation/GaussianSpectrum.gaussian_mass_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/GaussianSpectrum.gaussian_mass_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is C>0 such that the total multiplicity-weighted Gaussian mass is at most C M log(2+M) for every M at least one. Split at ordinate 4M, use the counting bound on the finite part, and apply the inverse-square tail estimate to the remaining Gaussian coefficients.

**Theorem 1.8 (Transition-band mass).**

Lean statement: `D5/S3/Analytic/Oscillation/GaussianSpectrum.transition_mass_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/GaussianSpectrum.transition_mass_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every unit window starting at t>=0 has multiplicity at most A log(t+3), there is C>0 such that N(M+Delta)-N(M) is at most C Delta log(2+M) whenever 1<=Delta<=M. Cover the interval by the ceiling of Delta unit windows and telescope their counts.

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/GaussianSpectrum.abs_gaussianCos_le`
- Truth anchor: `D5/S3/Analytic/Oscillation/GaussianSpectrum.count_bound`
- Truth anchor: `D5/S3/Analytic/Oscillation/GaussianSpectrum.gaussianCos_continuous`
- Truth anchor: `D5/S3/Analytic/Oscillation/GaussianSpectrum.gaussianCos_summable`
- Truth anchor: `D5/S3/Analytic/Oscillation/GaussianSpectrum.gaussian_coefficients_summable`
- Truth anchor: `D5/S3/Analytic/Oscillation/GaussianSpectrum.gaussian_mass_bound`
- Truth anchor: `D5/S3/Analytic/Oscillation/GaussianSpectrum.inverse_square_summable`
- Truth anchor: `D5/S3/Analytic/Oscillation/GaussianSpectrum.transition_mass_bound`
- Dependency: [D5/S3/Analytic/Oscillation/OrdinateCounting](OrdinateCounting.md)
