# The moving-cutoff estimate for irrational Poisson jumps

## Abstract

Irrational jump ratios give annular damping and decay of the full moving-cutoff Fourier error.

**Theorem 1.1 (The full moving-cutoff Fourier error vanishes).**

Lean statement: `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworthCutoff.symmetric_cutoff_vanishes`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworthCutoff.symmetric_cutoff_vanishes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Junwei Lu and StatLean contributors (2026). *StatLean Fourier smoothing and Gaussian Hermite suppliers*. URL: <https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254>.

*Commentary.*

Assume p and q are positive, b is nonzero, and a divided by b is irrational. For every fixed positive C, w times the characteristic-function error integral over the symmetric interval from minus Cw to Cw tends to zero. The comparison uses variance V and the raw third jump moment.

Irrationality prevents both cosine terms from attaining one at a nonzero frequency. Compactness therefore gives a positive damping gap on each fixed annulus. The low-frequency Gaussian estimate, this annular gap, and an integrable Gaussian correction tail control the whole interval.

## References

- Truth anchor: `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworthCutoff.symmetric_cutoff_vanishes`
- Dependency: [D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworthFoundation](CompoundPoissonEdgeworthFoundation.md)
