# Global Sieve

## Abstract

Global Sieve

Adelic sieve: one-sided Poisson summation per pivot, frequency sum bound, final sieve inequality.

**Theorem 1.1 (sieve).**

Lean statement: `D5/S3/Zeros/GRH/New/Filling/GlobalSieve.sieve`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Filling/GlobalSieve.sieve` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

The sieve, under Filling.IsAdmissible: for the forms J_v of the Bessel systems, a system J' at T (bounds e, finHeadWeight, Filling.frequencyGain), finite sets U ⊂ A of T-units, g⁻¹ a T-integer: Re ∑_{t∈U, p,q∈A^ϱ} J'∏J_v ≤ vol(Ô)^(ϱ+1)∏l(v,i)⁻²·(e∏_v((1+b⁻¹⁰)/deg_v) + b^(−6kf−10)/deg).

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Filling/GlobalSieve.sieve`
- Dependency: [D5/S3/Zeros/GRH/Lib/Adelic/Adeles/FinitePlaceDensity](../../Lib/Adelic/Adeles/FinitePlaceDensity.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/RealConvolution](../../Lib/Adelic/CuspForms/RealConvolution.md)
- Dependency: [D5/S3/Zeros/GRH/New/Filling/NearTerms](NearTerms.md)
