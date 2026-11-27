# Frobenius Factors

## Abstract

Frobenius Factors

Frobenius-power products of generic matrices: monomial weights track the excess up to error.

**Theorem 1.1 (pow_dvd_coeff_conj_frobOperator).**

Lean statement: `D5/S3/Zeros/GRH/New/TwistedHecke/FrobeniusFactors.pow_dvd_coeff_conj_frobOperator`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/TwistedHecke/FrobeniusFactors.pow_dvd_coeff_conj_frobOperator` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let a' = a+1, Nnk(ℓ+2) ≤ P^ℓ, ℓ ≤ N, and, for j = s − d and e = P^d, ψ(s,d) = ι_s(h)(ι_j(h)⁻¹g_jι_j(h))^{(e)}ι_s(h)⁻¹ (entrywise powers). In row β of TwistingData.frobOperator, w^c divides the coefficient of ν if ν_j has equal row and column TwistingData.indexWeight-weights for j ≠ i and |excess of β at i+ℓ − row weight of ν_i| > 2c+1.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/TwistedHecke/FrobeniusFactors.pow_dvd_coeff_conj_frobOperator`
- Dependency: [D5/S3/Zeros/GRH/New/TwistedHecke/RootLemma](RootLemma.md)
