# The Cauchy lower coefficient at exact phase alignment

## Abstract

Exact phase alignment turns the leading count into a lower bound for the ordered pair sum.

**Theorem 1.1 (A lower coefficient for fully aligned cutoffs).**

Lean statement: `D5/S3/Analytic/Oscillation/MontgomeryAlignmentLower.eventually_montgomery_gt_of_sine_alignment`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/MontgomeryAlignmentLower.eventually_montgomery_gt_of_sine_alignment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N(Y) be the inclusive multiplicity-weighted count with N(Y)/(Y log Y) tending to c = 1/(2π). For each κ < 2πc² and all sufficiently large Y, any real t at which every sine sin(tγ) through Y equals one has an ordered Lorentz pair sum strictly greater than κY(log Y)².

At alignment, each difference cosine is one. Use the real multiplicities as coefficients and apply the Cauchy lower bound on the buffered interval with radius √Y. The retained fraction 2 arctan(√Y)/π tends to one, and the normalized buffer length tends to one. The normalized count then gives the limiting lower coefficient.

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/MontgomeryAlignmentLower.eventually_montgomery_gt_of_sine_alignment`
- Dependency: [D5/S3/Analytic/Oscillation/MontgomeryWindow](MontgomeryWindow.md)
- Dependency: [D5/S3/Analytic/Oscillation/SpectrumPhaseCutoff](SpectrumPhaseCutoff.md)
- Dependency: [D5/S3/Fourier/Concentration/CauchyPairEnergy](../../Fourier/Concentration/CauchyPairEnergy.md)
