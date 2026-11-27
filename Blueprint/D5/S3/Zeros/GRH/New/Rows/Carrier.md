# Carrier

## Abstract

Carrier

Matched identity summed on a square block; datum reduces to one coset's class sum. Exchange of theta kernels with explicit determinant polynomials and Hecke L-value constant. Twisted theta class sums equal Hecke-value multiples of a constant and of the carrier.

**Theorem 1.1 (stdClassSum_carrierXi_eq_carrierForm).**

Lean statement: `D5/S3/Zeros/GRH/New/Rows/Carrier.stdClassSum_carrierXi_eq_carrierForm`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Rows/Carrier.stdClassSum_carrierXi_eq_carrierForm` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let m > 0 be even. For some C, every c of weight 0, tame for (𝔪, χ), has γ with |γ|² = C/(nL(cυ^{m/2}, m/2)·nL(c⁻¹υ^m, m)) and γ·Σ_h carrierXi(h)·θ_{υ^m,c}[χ∘det, 1](x, h) = carrierForm(x) for all x; nL = lValueProd at the places of 𝔪.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Rows/Carrier.stdClassSum_carrierXi_eq_carrierForm`
- Dependency: [D5/S3/Zeros/GRH/New/Exchange/ExchangeTheorem](../Exchange/ExchangeTheorem.md)
- Dependency: [D5/S3/Zeros/GRH/New/Rows/RealMatching](RealMatching.md)
