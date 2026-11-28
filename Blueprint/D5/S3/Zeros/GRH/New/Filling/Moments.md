# Moments

## Abstract

Moments

Trace of a small central projection on the Bessel-subgroup terms is small. Sharp bound for the second moment over elements fixing vectors with unit minors. Moment bounds for the Poincaré series and spread of translates modulo any subspace.

**Theorem 1.1 (exists_translate_finrank_comap_le).**

Lean statement: `D5/S3/Zeros/GRH/New/Filling/Moments.exists_translate_finrank_comap_le`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Filling/Moments.exists_translate_finrank_comap_le` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Filling: let ρ be unitary, ⟨ρ(s)Qe_y, Qe_x⟩ = c·(amplitude sums), c > 0, R = ρ(∏g_i) for central idempotents with Re(1−g_i)(1) ≤ b⁻⁸/2, rank R ≤ |𝖦|·deg·mass. Each subspace F of im R, of share φ, has an s with dim (Rρ(s)Q)⁻¹F ≤ ½(1 + φ + 19b⁻⁴)D_c.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Filling/Moments.exists_translate_finrank_comap_le`
- Dependency: [D5/S3/Zeros/GRH/New/Filling/CrudeEnergy](CrudeEnergy.md)
- Dependency: [D5/S3/Zeros/GRH/New/Filling/FiniteSystem](FiniteSystem.md)
- Dependency: [D5/S3/Zeros/GRH/New/Heights/OneDeterminant](../Heights/OneDeterminant.md)
- Dependency: [D5/S3/Zeros/GRH/New/Trace/BadShare](../Trace/BadShare.md)
