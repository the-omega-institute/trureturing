# Fundamental Domain

## Abstract

Fundamental Domain

Fourier inversion and uniqueness on a compact abelian quotient, via Stone-Weierstrass. Mean over compact quotient equals fundamental-domain average; unfolding of sums over a lattice. Bounded fundamental domain for a number field in adeles, with its volume.

**Theorem 1.1 (exists_fundDomain_prod).**

Lean statement: `D5/S3/Zeros/GRH/Lib/General/Analysis/FundamentalDomain.exists_fundDomain_prod`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/General/Analysis/FundamentalDomain.exists_fundDomain_prod` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let j = (j₁, j₂): I → V×W be additive on the number field I, j₁ the Minkowski embedding up to a measure-preserving isomorphism, j₂⁻¹(O) = J, W = j₂(I) + O. Then F×O is a strict fundamental domain for some bounded measurable F of volume N(J)2^(−r₂)√|disc I|.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/General/Analysis/FundamentalDomain.exists_fundDomain_prod`
- Dependency: [D5/S3/Zeros/GRH/Lib/Adelic/QuotientMeasure/PeriodicMean](../../Adelic/QuotientMeasure/PeriodicMean.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Adelic/QuotientMeasure/Unimodular](../../Adelic/QuotientMeasure/Unimodular.md)
