# Thin Classes

## Abstract

Thin Classes

Schur-test bound for total amplitude of a thin double-coset class of terms.

**Theorem 1.1 (tsum_amplitudeAbs_class_le).**

Lean statement: `D5/S3/Zeros/GRH/New/Filling/ThinClasses.tsum_amplitudeAbs_class_le`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Filling/ThinClasses.tsum_amplitudeAbs_class_le` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let γ have level j, lie over (c, s, c') and satisfy ∏_v|𝗀(γ)|_v ≤ N^f·Filling.minorNorm j γ. Then the absolute amplitudes, for cut Bessel functions, over the double coset 𝖴⁰_c(g)γ𝖴⁰_c'(g) sum to at most ν·Filling.classSize j (𝗀*), 𝗀* = Filling.classGauge j c c' γ, ν = Filling.unipCovolume.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Filling/ThinClasses.tsum_amplitudeAbs_class_le`
- Dependency: [D5/S3/Zeros/GRH/New/Filling/SchurTest](SchurTest.md)
