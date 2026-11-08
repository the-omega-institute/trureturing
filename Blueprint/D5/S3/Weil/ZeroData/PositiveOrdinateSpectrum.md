# The positive zeta ordinate spectrum

## Abstract

Under RH, positive zeta zeros give a locally finite spectrum with faithful multiplicities.

**Definition 1.1 (Spectrum from positive nontrivial zeta zeros).**

Lean statement: `D5/S3/Weil/ZeroData/PositiveOrdinateSpectrum.zetaSpectrum`

*Formalization.* `D5/S3/Weil/ZeroData/PositiveOrdinateSpectrum.zetaSpectrum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The indices are the distinct nontrivial complex zeta zeros with positive imaginary part. Each ordinate is the imaginary part, and each multiplicity is the canonical analytic zero multiplicity. RH puts every zero on the critical line, so equal ordinates imply equal indices. Canonical local finiteness gives finite upper cutoffs.

**Theorem 1.2 (Exact identification of cutoff counts).**

Lean statement: `D5/S3/Weil/ZeroData/PositiveOrdinateSpectrum.zetaSpectrum_N`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/PositiveOrdinateSpectrum.zetaSpectrum_N` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real T the spectrum count is exactly the canonical count in the window (0,T]. The bijection sends each subtype index to its underlying complex zero and preserves multiplicity.

**Theorem 1.3 (Classical logarithmic spectrum count).**

Lean statement: `D5/S3/Weil/ZeroData/PositiveOrdinateSpectrum.zetaSpectrum_countAsymptotic`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/PositiveOrdinateSpectrum.zetaSpectrum_countAsymptotic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under RH, the spectrum count divided by T log T tends to 1/(2 pi). The cumulative counting theorem uses the unconditional Riemann-von Mangoldt source; RH is used to construct an injective ordinate spectrum.

## References

- Truth anchor: `D5/S3/Weil/ZeroData/PositiveOrdinateSpectrum.zetaSpectrum`
- Truth anchor: `D5/S3/Weil/ZeroData/PositiveOrdinateSpectrum.zetaSpectrum_N`
- Truth anchor: `D5/S3/Weil/ZeroData/PositiveOrdinateSpectrum.zetaSpectrum_countAsymptotic`
- Dependency: [D5/S3/Analytic/Oscillation/OrdinateCounting](../../Analytic/Oscillation/OrdinateCounting.md)
- Dependency: [D5/S3/Weil/ZeroData/CumulativeRiemannVonMangoldt](CumulativeRiemannVonMangoldt.md)
