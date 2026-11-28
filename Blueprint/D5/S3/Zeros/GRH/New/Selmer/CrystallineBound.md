# Crystalline Bound

## Abstract

Crystalline Bound

Case analysis on ℓ bounding crystalline classes modulo those orthogonal to congruent lattices.

**Theorem 1.1 (crystalline_defect_le).**

Lean statement: `D5/S3/Zeros/GRH/New/Selmer/CrystallineBound.crystalline_defect_le`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Selmer/CrystallineBound.crystalline_defect_le` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Local loss, crystalline case. Let L be crystalline with jumps in U'; let U, U' lie in opposite windows Lift.IsInJumpWindow at b + δ (thick) or G + δ (thin), with the listed conditions on sizes and on a Kummer chart. Assume U' lies in [−η, 0], or negative members of U' and negative members of U are ≤ −h/2 with ≤ μ jumps per embedding in [−η, η]. Then Z_f(L) modulo Lift.cupOrthogonal for crystalline lattices with jumps in U has normalised length ≤ [G_ℓ : j(Γ)]·y if y ≥ 10⁵(rk L·⌊2λ/Q⌋·m + μλ), λ = lambdaLoss.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Selmer/CrystallineBound.crystalline_defect_le`
- Dependency: [D5/S3/Zeros/GRH/New/Lift/ExponentTheorems](../Lift/ExponentTheorems.md)
- Dependency: [D5/S3/Zeros/GRH/New/Selmer/CrystallineRank](CrystallineRank.md)
