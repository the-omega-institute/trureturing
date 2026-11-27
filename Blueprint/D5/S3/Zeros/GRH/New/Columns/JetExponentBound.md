# Jet Exponent Bound

## Abstract

Jet Exponent Bound

Marked primes at inert p: orders of -p, parity, balance; scaled Hecke operator. Sum of jet exponents along the chain is at least gain minus error.

**Theorem 1.1 (sum_lowColumns_le).**

Lean statement: `D5/S3/Zeros/GRH/New/Columns/JetExponentBound.sum_lowColumns_le`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Columns/JetExponentBound.sum_lowColumns_le` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For marked Λ and j < m: #Λ·δ_p + 𝔯·∑_σ Data.lowColumns j σ ≤ loss(p)/m + #(even tops)·a/x₁, the sum over the even places σ (those inducing a prime in Λ), with δ_p = Data.deltaP p.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Columns/JetExponentBound.sum_lowColumns_le`
- Dependency: [D5/S3/Zeros/GRH/New/Exchange/CrudeModularData](../Exchange/CrudeModularData.md)
