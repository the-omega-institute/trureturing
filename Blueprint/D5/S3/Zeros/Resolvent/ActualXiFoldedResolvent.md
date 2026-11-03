# The original xi folded resolvent

## Abstract

The original xi folded resolvent.

**Theorem 1.1 (The original xi folded resolvent).**

Lean statement: `D5/S3/Zeros/Resolvent/ActualXiFoldedResolvent.actual_xi_folded_hasSum`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Resolvent/ActualXiFoldedResolvent.actual_xi_folded_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The independent function xiOdd(w) is (i times logDeriv xiReading at one half minus i w, minus the original real firstLiMass times w), divided by w squared plus one quarter. It is defined directly from the existing xiReading and is never defined by a spectral series.

The positive-height square-resolvent HasSum supplier and the original complex endpoint-mass HasSum are reused with the canonical actualData. Reflection folds the mass to twice each positive-height contribution. Subtracting these two convergent sums first, and then dividing by the common denominator, gives the exact summand w times weight divided by one minus node times w squared. No divergent reciprocal-zero sums are split.

The HasSum identity holds for every complex w with norm less than one quarter, including zero. The entire square-source logDeriv composition and xi reflection pay the center without dividing by w. The actual height exclusion proves the required xi nonvanishing on this disk; it is not an added convergence or zero-free hypothesis. Off-line zeros and all analytic multiplicities remain present.

## References

- Truth anchor: `D5/S3/Zeros/Resolvent/ActualXiFoldedResolvent.actual_xi_folded_hasSum`
- Dependency: [D5/S3/Zeros/Resolvent/ActualXiFoldedSpectrum](ActualXiFoldedSpectrum.md)
