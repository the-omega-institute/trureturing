# Montgomery windows for finite cosine sums

## Abstract

Averaged pair correlation forces mean-square mass in a logarithmic window.

**Theorem 1.1 (Mean-square mass in the hard cosine window).**

Lean statement: `D5/S3/Analytic/Oscillation/MontgomeryWindow.hard_window_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/MontgomeryWindow.hard_window_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a locally finite positive spectrum with positive integer multiplicities, and assume N(T)/(T log T) tends to 1/(2 pi). Define C_M(y) as the multiplicity-weighted sum of cos(gamma y) over ordinates at most M. Define F(alpha,T) by the double cosine sum with weight 4/(4+(gamma-gamma')^2) and normalization 2 pi/(T log T). Assume that for every epsilon>0, the integral of F(alpha,T) over [17,19] is eventually at least 2/3-epsilon. Then, for all sufficiently large M, the integral of C_M(y)^2 over [16 log M,20 log M] is at least c M(log M)^2, where c=1/(32 pi).

The kernel h(v)=exp(-2 abs(v)) has mass one and cosine transform 4/(4+t^2), obtained by rescaling the two-sided exponential transform. Expanding the smoothed square separates the difference frequencies, whose integral is determined by F, from the sum frequencies. For a fixed cutoff R, the absolute sum-frequency contribution is bounded by N(R)^2 plus eight times N(M) times the inverse-square tail above R. The counting asymptotic and the inverse-square tail bound make this contribution o(M log M). Fubini and positivity localize the smoothed square: shifts of absolute value at most log M stay in the larger window, while the remaining kernel mass is exp(-2 log M). The resulting leakage is at most 2 log M N(M)^2 exp(-2 log M), which is o(M(log M)^2).

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/MontgomeryWindow.hard_window_lower`
- Dependency: [D5/S3/Analytic/Oscillation/OrdinateCounting](OrdinateCounting.md)
