# An unweighted autocorrelation limit for finite spectral cutoffs

## Abstract

Autocorrelation from the Montgomery unit band

**Theorem 1.1 (Autocorrelation from the Montgomery unit band).**

Lean statement: `D5/S3/Analytic/Oscillation/MontgomeryAutocorrelationLimit.spectral_unweighted_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/MontgomeryAutocorrelationLimit.spectral_unweighted_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume bounded two-term counting discrepancy at every real height at least two pi and a uniform Montgomery profile on the unit band. For a real Schwartz test with Fourier support in the unit band, form the sum of its autocorrelation over all ordered pairs of ordinates through H at the mean spacing scale. Include all multiplicities. Divide by H log H over two pi.

The quotient tends to the square of the integral of the test plus its Fourier energy weighted by absolute frequency. The Fourier transform of the autocorrelation is the squared modulus of the Fourier transform of the test. The exponential peak in the profile becomes an approximate identity of mass one, and the uniform remainder gives a vanishing integrated error.

Bounded discrepancy bounds the number of atoms in each scaled distance shell. Rapid decay of the autocorrelation controls the shell sum of the change from the Lorentz pair weight to one. After counting normalization the cost tends to zero.

**Theorem 1.2 (Unweighted autocorrelation from convergence against fixed tests).**

Lean statement: `D5/S3/Analytic/Oscillation/MontgomeryAutocorrelationLimit.spectral_unweighted_limit_of_test_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/MontgomeryAutocorrelationLimit.spectral_unweighted_limit_of_test_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same spectrum, assume that for every fixed real Schwartz test with Fourier support on the unit band, integrating the Montgomery profile against its squared Fourier modulus tends to the square of the test integral plus the Fourier energy weighted by absolute frequency. If a single bound controls the two-term counting discrepancy at every real height at least two pi, the unweighted autocorrelation sum of that test has the same limit after division by H log H over two pi.

The Fourier integral equals the normalized Lorentz-weighted autocorrelation at the same cutoff. The bound on the number of ordinates per scaled distance shell makes the normalized cost of removing the Lorentz weight tend to zero.

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/MontgomeryAutocorrelationLimit.spectral_unweighted_limit`
- Truth anchor: `D5/S3/Analytic/Oscillation/MontgomeryAutocorrelationLimit.spectral_unweighted_limit_of_test_limit`
- Dependency: [D5/S3/Analytic/Oscillation/MontgomeryWindow](MontgomeryWindow.md)
- Dependency: [D5/S3/Analytic/Oscillation/SmoothedSpectrumCounting](SmoothedSpectrumCounting.md)
