# Jet Divisibility

## Abstract

Jet Divisibility

Tilting matrices that kill Frobenius pairings at controlled determinant cost. Lower bound for valuations of Schur jets when Frobenius couplings are silenced.

**Theorem 1.1 (norm_schurJet_le).**

Lean statement: `D5/S3/Zeros/GRH/New/Curve/JetDivisibility.norm_schurJet_le`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Curve/JetDivisibility.norm_schurJet_le` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Divisibility of Schur jets. Let κ fit, with B boxes, |ϖ| = p^{−ρ}, |θ| = p^ω, and let the charges g be nonzero at one end of each coupling exempted by the even places ev. If IsIntegralOnNullCone holds up to degree B, each entry of the jet matrix along S_κ has valuation ≥ (1/(p−1) − ρ)B + ω∑couplingCount − |Φ||n′|³(⌊log_p B⌋ + 1) − m, m the total charge of the boxes of its row.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Curve/JetDivisibility.norm_schurJet_le`
- Dependency: [D5/S3/Zeros/GRH/New/Core/ModuleIndex](../Core/ModuleIndex.md)
- Dependency: [D5/S3/Zeros/GRH/New/Curve/LiveSum](LiveSum.md)
