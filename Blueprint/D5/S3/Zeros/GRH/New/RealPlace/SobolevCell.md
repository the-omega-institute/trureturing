# Sobolev Cell

## Abstract

Sobolev Cell

Lower bound for Haar integral via open-cell double coset chart, explicit constant. Unfolding bound over the Bessel unipotent group when frame entries stay bounded. Schur's bound read at one section point, via Sobolev chain in derivative words.

**Theorem 1.1 (lintegral_gramSection_integral_le).**

Lean statement: `D5/S3/Zeros/GRH/New/RealPlace/SobolevCell.lintegral_gramSection_integral_le`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/RealPlace/SobolevCell.lintegral_gramSection_integral_le` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let F satisfy HasSchurBound with constants P ≥ 8r, D; let 𝗀 ≥ c > 0 and IsBoundedInCell (bound P) hold within P⁻⁶ of Z; let φ be measurable, integrable, zero where ‖y‖ > P²⁰. Then c_G c^{k−1} ∬ ‖∫ φ(y)F(γ_Z(uh)⁻¹y) dy‖² dh du ≤ P^{2000(ϱ+1)²} D ∫|φ|², over h ∈ U(κ), u ∈ 𝖴⁰, ‖u‖ ≤ P²⁰.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/RealPlace/SobolevCell.lintegral_gramSection_integral_le`
- Dependency: [D5/S3/Zeros/GRH/New/RealPlace/BesselOrthonormal](BesselOrthonormal.md)
