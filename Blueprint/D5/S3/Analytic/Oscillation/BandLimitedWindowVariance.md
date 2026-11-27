# Band-limited Schwartz windows with uniform variation

## Abstract

Fourier variance of band-limited windows

**Theorem 1.1 (Fourier variance of band-limited windows).**

Lean statement: `D5/S3/Analytic/Oscillation/BandLimitedWindowVariance.exists_windows_with_unbounded_spectral_variance`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/BandLimitedWindowVariance.exists_windows_with_unbounded_spectral_variance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is a constant K greater than or equal to zero such that for each natural number n a real Schwartz function g has Fourier transform supported in the closed unit band, integral of its absolute derivative at most K, and weighted Fourier energy at least n divided by four pi squared. The weight in the energy is the absolute value of frequency.

Take the inverse Fourier transform of an even smooth bump which equals one on a neighborhood of zero. Integrating that real function over a sliding interval gives a Schwartz window. Its derivative is the difference of the two translates at the interval endpoints, so its integral of absolute derivative is at most twice the integral of the absolute value of the original function.

The Fourier transform of the interval contributes a sine divided by frequency. On each interval between consecutive points of the form two to the power j times pi, the integral of sine squared divided by its argument is at least one quarter. A suitable window width places n of these intervals in the band where the smooth bump is one.

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/BandLimitedWindowVariance.exists_windows_with_unbounded_spectral_variance`
