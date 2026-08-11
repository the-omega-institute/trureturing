# Wigner-Yanase Spectrum Ordering

## Abstract

The five members of the Wigner-Yanase contraction spectrum are strictly increasing.

**Theorem 1.1 (The five-member Wigner-Yanase spectrum is strictly ordered).**

$$1 < \frac{1}{2(1 - \ln 2)} < 2 < \frac{6}{11 - 12\ln 2} < \frac{1}{1 - \ln 2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/WignerYanaseSpectrum.wy_contraction_spectrum_strict_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Wigner-Yanase contraction spectrum reported for the divergence tower consists of the five values 1, 1/(2(1 − ln 2)), 2, 6/(11 − 12 ln 2), and 1/(1 − ln 2), where ln 2 denotes the natural logarithm of two. Using the elementary bounds 0.6931471803 < ln 2 < 0.6931471808 (so that 1 − ln 2 > 0 and 11 − 12 ln 2 > 0), each successive strict inequality reduces to a linear bound on ln 2 and is discharged by clearing the positive denominators.

The theorem establishes only this strict ordering of the reported spectrum values; it does not derive why these are the Wigner-Yanase contraction coefficients, nor does it cover the J-relations or the partner-anonymity clause of the note.

## References
