# The counting obstruction from a uniform Montgomery profile

## Abstract

Unbounded count discrepancy from the Montgomery unit band

**Theorem 1.1 (Unbounded count discrepancy from the Montgomery unit band).**

Lean statement: `D5/S3/Analytic/Oscillation/MontgomeryCountDiscrepancy.unit_band_profile_forces_unbounded_count_discrepancy`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/MontgomeryCountDiscrepancy.unit_band_profile_forces_unbounded_count_discrepancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a locally finite spectrum of positive ordinates with positive integer multiplicities. Let N(H) count all copies through the inclusive cutoff H. For each ordered pair through H let d be the first ordinate minus the second. Define P_H(alpha) by summing cos(alpha log(H) d) times 4/(4+d^2) times the product of the two multiplicities, and multiply the sum by 2 pi/(H log(H)).

Suppose c(H) tends to one and e(H) tends to zero. For every sufficiently large real H and all real alpha with abs(alpha) at most one, assume the absolute difference between P_H(alpha) and c(H) log(H) exp(-2 log(H) abs(alpha)) + abs(alpha) is at most e(H).

Write F(H) = H/(2 pi) times (log(H/(2 pi)) - 1). For every real threshold H0 and every real D there exists a real H at least H0 such that abs(N(H) - F(H)) exceeds D.

Under bounded discrepancy, compare the smoothed count to the truncated reference density. If U bounds the cumulative discrepancy and A is the integral of the absolute derivative of the test, the limiting centered variance is at most (U A)^2. The test family has A at most a single constant K, giving the common bound (U K)^2. For each fixed test, let H tend to infinity. The autocorrelation limit identifies the centered variance with the weighted Fourier energy after dropping the vanishing exterior first and second moments. Choosing larger windows then forces this energy past the bound shared by all windows.

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/MontgomeryCountDiscrepancy.unit_band_profile_forces_unbounded_count_discrepancy`
- Dependency: [D5/S3/Analytic/Oscillation/BandLimitedWindowVariance](BandLimitedWindowVariance.md)
- Dependency: [D5/S3/Analytic/Oscillation/MontgomeryAutocorrelationLimit](MontgomeryAutocorrelationLimit.md)
