# The Cauchy lower coefficient at exact phase alignment

## Abstract

Exact phase alignment turns the leading count into a lower bound for the ordered pair sum.

**Theorem 1.1 (A lower coefficient for fully aligned cutoffs).**

Lean statement: `D5/S3/Analytic/Oscillation/MontgomeryAlignmentLower.eventually_montgomery_gt_of_phase_alignment`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/MontgomeryAlignmentLower.eventually_montgomery_gt_of_phase_alignment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N(Y) be the inclusive multiplicity-weighted count with N(Y)/(Y log Y) tending to c = 1/(2π). For each κ < 2πc² and all sufficiently large Y, any real t for which every pair through Y satisfies cos(t(γ−γ′)) = 1 has an ordered Lorentz pair sum strictly greater than κY(log Y)². The condition holds at zero frequency and whenever all individual phases agree modulo 2π.

With each difference cosine equal to one, use the positive multiplicities as coefficients and apply the Cauchy lower bound on the buffered interval with radius √Y. The retained fraction 2 arctan(√Y)/π tends to one, and the normalized buffer length tends to one. The normalized count then gives the limiting lower coefficient.

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/MontgomeryAlignmentLower.eventually_montgomery_gt_of_phase_alignment`
- Dependency: [D5/S3/Analytic/Oscillation/MontgomeryWindow](MontgomeryWindow.md)
- Dependency: [D5/S3/Analytic/Oscillation/SpectrumPhaseCutoff](SpectrumPhaseCutoff.md)
- Dependency: [D5/S3/Fourier/Concentration/CauchyPairEnergy](../../Fourier/Concentration/CauchyPairEnergy.md)
